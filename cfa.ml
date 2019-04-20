(** Control flow analysis module implementing 0CFA. *)

open Binding
open Grammar
open GrammarCommon
open HGrammar
open Utilities

(* --- types --- *)

module SortedHTermsIds = SortedList.Make(struct
    type t = hterms_id
    let compare = Pervasives.compare
  end)

type hterms_ids = SortedHTermsIds.t

module HTermSet = Set.Make (struct
    type t = hterm
    let compare = Pervasives.compare
  end)

class cfa (hg : hgrammar) = object(self)
  (* --- state of 0CFA --- *)

  (** Queue of hterms to process. Eventually all reachable hterms are processed. Note that aside
      from hterms that are present in the grammar, hterms with more variables can be processed
      too when a partially applied hterm was an argument to a nonterminal, and was substituted for
      a variable in this nonterminal gaining additional arguments. Some extra hterms may be
      processed, since all possibilities are iterated over when encountering a variable, without
      regard for context. *)
  val mutable hterm_queue : hterm list = []

  (** A set of hterms that were already processed kept to not process them again. *)
  val mutable visited_nodes : HTermSet.t = HTermSet.empty
  
  (* --- output of 0CFA --- *)

  (* TODO do cleanup on what needs to be sorted and what is guaranteed to not be duplicated when
     inserting it. *)

  (** hterms_are_arg[id] contains a boolean whether hterms with given id can possibly be an
      argument to a nonterminal. It contains exactly the ids of hterms may be an argument to
      a nonterminal according to 0CFA, so there may be false positives. *)
  val hterms_are_arg : bool array = Array.make hg#hterms_count false

  (** nt_bindings[nt] contains a list of bindings for nonterminal nt. Each binding corresponds
      to a possible application of nonterminal nt detected by 0CFA and is a list of tuples
      (i, j, id) stating that hterms identified by id are arguments from i-th to j-th (0-indexed)
      in given application.
      In short, this tells which lists hterms flow into which arguments of a nonterminal. *)
  val nt_bindings : hterms_id binding list array = Array.make hg#nt_count []

  (** var_bindings[nt][i] contains a list of hterms that may be i-th argument (0-indexed) to
      nonterminal nt according to 0CFA. *)
  val var_bindings : hterm list array array =
    Array.init hg#nt_count (fun i -> Array.make (hg#nt_arity i) [])

  (** nt_bindings_applied_to_hterms[id] contains tuples of nonterminal ids and hterms bindings
      under which these nonterminals were applied to hterms identified by id. *)
      (* TODO after implementing eager flag - that is only if either Flags.eager is false or
         nt has a head variable in its definition. *)
  val nt_bindings_applied_to_hterms : (nt_id * hterms_id binding) list array =
    Array.make hg#hterms_count []

  (** variable_head_nodes[nt][i] is a list of processed hterms that have variable (nt, i) as
      head, i.e., i-th variable in definition of nonterminal nt. Internal for this module. *)
  (* TODO cleanup of docs *)
  val variable_head_nodes : hterm list array array = Array.make hg#nt_count [||]

  (** array_headvars[f] is a list of head variables in nonterminal's definition, i.e., variables
      that are applied to something. *)
  (* TODO cleanup of docs *)
  val array_headvars : vars array = Array.make hg#nt_count SortedVars.empty

  (** hterms_where_hterms_flow[id] contains a list of ids of hterms that contain a variable that
      could be substituted with a hterm from hterms idenfitied by id. In other words, this is a
      list of ids of hterms where hterms idenfified by id flow. *)
  val hterms_where_hterms_flow : hterms_ids array =
    Array.make hg#hterms_count SortedHTermsIds.empty

  (** hterms_bindings[id] describes which hterms (sequences of terms) substitute which
      variables in hterms identified by id.
      Each binding is a list of tuples (i, j (v, h)) that describes that hterms identified by h
      were arguments from i-th to j-th (0-indexed) to a nonterminal nt in which hterms identified
      by id are defined, and that variables with indexes v (i.e., (nt, x) for all x in v) were
      substituted with hterms identified by h. *)
  val hterms_bindings : hterms_id binding list array = Array.make hg#hterms_count []

  (** hterms_containing_nt[nt] is a list of ids of hterms whose definitions contain nonterminal
      nt and these hterms were used as an argument to some nonterminal. *)
  val hterms_containing_nt : hterms_ids array = Array.make hg#nt_count SortedHTermsIds.empty
  
  (** nt_containing_nt[nt] contains ids of all nonterminals that have nonterminal with id nt
      present in their body. *)
  (* TODO when adding linearity - except for ones present in nt_containing_nt_lin[nt]. *)
  val nt_containing_nt : nts array = Array.make hg#nt_count SortedNTs.empty

  (* If Flags.incremental is false then nt_containing_nt_linearly[f] contains list of nonterminals g that
      have f present in their body exactly once at root or applied a number of times to a terminal,
      i.e., t1 .. (t2 .. (tN (f arg1 .. argK) ..) ..) .. for some terminals tX and terms argY. *)
  (* TODO cleanup of docs, unused for now *)
  (*
  val nt_containing_nt_linearly : nts array = Array.make hg#nt_count SortedNTs.empty
  *)

  (* --- access --- *)

  method hterms_are_arg (id : hterms_id) : bool =
    hterms_are_arg.(id)
  
  method has_head_vars (nt : nt_id) : bool =
    SortedVars.is_empty array_headvars.(nt)
  
  (* --- printing --- *)

  method string_of_binding (binding : hterms_id binding) : string=
    String.concat ", " @@ List.map (fun (i, j, id) ->
        string_of_int i ^ "-" ^ string_of_int j ^ " <- " ^ string_of_int id
      ) binding

  method string_of_binding_array : string =
    "bindings (nt -> bindings, one per line, comma-sep same-nt parts):\n" ^
    String.concat "\n\n" @@ array_listmap nt_bindings (fun nt binding ->
        hg#nt_name nt ^ ":\n" ^
        String.concat "\n" @@ List.map self#string_of_binding (nt_bindings).(nt)
      )
    
  (* --- TODO split into categories --- *)

  method add_index rho i =
    match rho with
    | [] -> []
    | ids :: rho' -> (* for each args_id *)
      (* check how many terms are under args_id *)
      let n = List.length @@ hg#id2terms ids in
      let j = i+n in
      (i, j - 1, ids) :: self#add_index rho' j (* each termsid is converted to (first_term_number, last_term_number, termsid), like (0, 3, ...);(4, 5, ...);(6, 11, ...), i.e., start and end positions on a concatenated list of all terms *)

  method register_nt_bindings_applied_to_hterms (id : hterms_id) (nt : nt_id)
      (binding : hterms_id binding) =
    let x = nt_bindings_applied_to_hterms.(id) in
    (* TODO make sure there are no copies *)
    nt_bindings_applied_to_hterms.(id) <- (nt, binding) :: x

  method get_nt_bindings_applied_to_hterms (id : hterms_id) : (nt_id * hterms_id binding) list =
    nt_bindings_applied_to_hterms.(id) 

  (** When there was an enqueued node f [id1, id2, ...] for some nonterminal f and args id id1, id2,
      ... and with states qs. ids are converted to a list of arguments through tab_id_terms.
      If we join all these lists, we get arg1, arg2, ..., where the position of each argument is
      position of argument in its idX plus length of arguments of previous lists that id(1..X-1)
      stand for.
      This function prepends to bindings a tuple (A, ref qs), where A is a list of (n, m, id), where
      id is the args_id from tab_id_terms, and n, n+1, ..., m are numbers that represent which
      arguments does that list stand for (e.g., arg3, arg4 in f arg1 arg2 arg3 arg4 arg5). *)
  method insert_nt_binding (args : int list) bindings = 
    let iargs = self#add_index args 0 in
    iargs::bindings

  method register_variable_head_node (v : var_id) (hterm: hterm) =
    let nt, i = v in
    let a = variable_head_nodes.(nt) in
    a.(i) <- hterm :: a.(i)

  (** Prepends term to list terms if it is not already there. Returns tuple of resulting list and
      boolean whether it was prepended to list. *)
  method insert_var_binding (term : 'a) (terms : 'a list) : 'a list * bool =
    if List.mem term terms then
      (terms, false)
    else
      (term :: terms, true)

  (*
  method print_hterm hterm =
    hg#print_hterm hterm
*)

  method enqueue_hterm hterm =
    hterm_queue <- hterm :: hterm_queue

  method dequeue_hterm =
    match hterm_queue with
    | [] -> None
    | x :: q ->
      hterm_queue <- q;
      Some x

  method enqueue_nodes nodes =
    List.iter self#enqueue_hterm nodes

  method expand_varheadnode term (hterm: hterm) =
    let h, termss = hterm in
    match h with
    | HVar x ->
      let (h', terms) = term in
      self#enqueue_hterm (h', terms@termss)
    | _ -> assert false

  (** Iterates (expand_varheadnode term) over everything in variable_head_nodes[nt_id][arg_id] *)
  method expand_varheadnodes nt i term =
    let nodes = variable_head_nodes.(nt).(i) in
    List.iter (self#expand_varheadnode term) nodes

  (** Called when term was i-th argument in a call f arg1 arg2 ...
      It makes sure that var_bindings[f][i] contains terms (H, [ID..]) that were
      i-th argument to nonterminal f, and calls expand_varheadnodes f i term when it was the first
      time adding it to var_bindings. *)
  method register_binding_singlevar nt i term =
    let tab = var_bindings.(nt) in (* var_bindings[nt_id][arg_id] = [...] *)
    let binds, changed = self#insert_var_binding term tab.(i) in (* making sure term is in var_bindings[nt_id][arg_id] *)
    if changed then (* if it was added just now *)
      begin
        tab.(i) <- binds; (* persist the addition *)
        self#expand_varheadnodes nt i term
      end

  method lookup_binding_var (nt, i) = 
    var_bindings.(nt).(i)

  (** converts rho to lists of args in form (H, [ID..]) as they would appear in
      f arg1 arg2 ...
      after all args_id lists of arguments were concatenated.
      Then it calls
      register_binding_singlevar f i arg_i
      for each arg_i = arg1, arg2, ..., i.e., that arg_i was i-th argument to which f was applied *)
  method register_var_bindings f rho i =
    match rho with
      [] -> ()
    | termsid :: rho' ->
      let hterms = hg#id2hterms termsid in (* convert args_id back to a list of (H, [ID..]) *)
      let hterms' = index_list hterms in (* numbering these terms *)
      List.iter (* for each term register_binding_singlevar f global-numbering-id hterm *)
        (fun (j, hterm)-> self#register_binding_singlevar f (i+j) hterm)
        hterms';
      self#register_var_bindings f rho' (i + List.length hterms) (* recursively *)

  (** Register information that there was a call f args, i.e., save this as a binding in
      nt_bindings and register in hterms_are_arg that args were an argument to nonterminal f. *)
  method register_binding (nt : int) (args : int list) =
    (* nt_bindings[nt] contains a list of
       ((number of first term in app, number of last term in app, args_id for first bundle of terms in app)::..., states under which visited) *)
    List.iter (fun id ->
        hterms_are_arg.(id) <- true
      ) args;
    nt_bindings.(nt) <- self#insert_nt_binding args nt_bindings.(nt);
    self#register_var_bindings nt args 0

  method lookup_nt_bindings (nt : nt_id) : hterms_id binding list =
    nt_bindings.(nt)

  (** Marking in visited_nodes a hterm that started being processed. *)
  method register_hterm (hterm : hterm) = 
    if HTermSet.mem hterm visited_nodes then
      failwith "Registering twice the same hterm";
    visited_nodes <- HTermSet.add hterm visited_nodes

  (** Enqueueing all argument hterms. The terminal does not matter. *)
  method expand_terminal termss =
    List.iter self#enqueue_hterm termss

  method process_hterm (hterm : hterm) =
    (* each hterm may be processed at most once *)
    if not @@ HTermSet.mem hterm visited_nodes then
      begin
        let h, h_args = hterm in
        (* saving that the hterm is already processed *)
        self#register_hterm hterm;
        (* expanding the calls to see what hterms go in what variables *)
        match h with
        | HT _ ->
          (* decoding arguments as hterm ids into hterms *)
          let _, termss = hg#decompose_hterm hterm in
          (* ignore the terminal and go deeper *)
          self#expand_terminal termss
        | HNT nt ->
          (* Remember in nt_bindings that there was an application f h_args. Also remember
             that h_args were being used as an argument to a nonterminal in hterms_are_arg. *)
          self#register_binding nt h_args;
          (* Enqueue the body hterm, ignoring all arguments. Note that arguments are not enqueued.
             If the arguments don't have kind O, they can be passed as arguments again, or used
             as variable head, which finds the original terms. *)
          self#enqueue_hterm @@ hg#nt_body nt
        | HVar x ->
          (* check what hterms flow into x (these can also be variables) *)
          let x_hterms = self#lookup_binding_var x in
          (* substitute these hterms into x and enqueue resulting application *)
          List.iter (fun (h, x_args) ->
              self#enqueue_hterm (h, x_args @ h_args)
            ) x_hterms;
          self#register_variable_head_node x hterm
      end

  (** Expand hterms in queue until it's empty. *)
  method expand : unit =
    match self#dequeue_hterm with
    | None ->
      print_verbose !Flags.verbose_preprocessing @@ lazy (
        self#string_of_binding_array ^ "\n" ^
        "Size of abstract control flow graph: " ^
        string_of_int (HTermSet.cardinal visited_nodes)
      )
    | Some hterm ->
      self#process_hterm hterm;
      self#expand

  (* --- accessing dependencies --- *)

  method get_hterms_containing_nt (nt : nt_id) =
    hterms_containing_nt.(nt)

  method get_nt_containing_nt (nt : nt_id) : nts =
    nt_containing_nt.(nt)

  method get_hterms_where_hterms_flow id =
    hterms_where_hterms_flow.(id)

  method get_hterms_bindings (id : hterms_id) : hterms_id binding list =
    hterms_bindings.(id)

  (*
  method get_nt_containing_nt_lin nt =
    nt_containing_nt_linearly.(nt)
  *)

  (* --- registering dependencies --- *)

  (** Appends hterm id2 to id1's list of hterms_where_hterms_flow. *)
  method register_hterms_where_hterms_flow id1 id2 =
    hterms_where_hterms_flow.(id1) <- SortedHTermsIds.merge hterms_where_hterms_flow.(id1) @@
      SortedHTermsIds.singleton id2

  method register_hterms_bindings id bindings =
    hterms_bindings.(id) <- bindings (* only place with actual modification *)
  
  (* nt occurs in the term id *)
  method private register_hterms_containing_nt nt id =
    (* note that this function can never be called with the same (nt,id) pair *)
    let ids = SortedHTermsIds.merge hterms_containing_nt.(nt) (SortedHTermsIds.singleton id) in
    hterms_containing_nt.(nt) <- ids

  method private register_dep_nt_nt nt1 nt2 =
    let nts = nt_containing_nt.(nt1) in
    let nts' = SortedNTs.merge (SortedNTs.singleton nt2) nts in
    nt_containing_nt.(nt1) <- nts'

  (*
  method register_dep_nt_nt_lin nt1 nt2 =
    let nts = nt_containing_nt_linearly.(nt1) in
    let nts' = SortedNTs.merge (SortedNTs.singleton nt2) nts in
    nt_containing_nt_linearly.(nt1) <- nts'
  *)

  (* --- computing dependencies --- *)

  (*
  method private print_binding_vars (vars : vars) =
    print_string "[";
    SortedVars.iter (fun (nt, i) -> print_string @@ string_of_int i ^ ",") vars;
    print_string "]"

  method print_binding_with_mask (binding : (vars * hterms_id) binding) =
    List.iter (fun (i, j, (vars, id)) ->
        print_string @@ "(" ^ string_of_int i ^ "," ^ string_of_int j ^ ",";
        self#print_binding_vars vars;
        print_string @@ ", " ^ string_of_int id ^ "), "
      ) binding; 
    print_string "\n"
  *)

  method string_of_hterms_bindings : string =
    "Dependency info (hterms_id -> [(from,to,hterms_id); ...]):\n" ^
    String.concat "\n" @@ List.filter (fun s -> s <> "") @@
    array_listmap hterms_bindings (fun id binding ->
        if hterms_are_arg.(id) then
          string_of_int id ^ ":\n" ^
          concat_map "\n" self#string_of_binding hterms_bindings.(id)
        else
          ""
      )

  (*
  (** Splits a list of vars to ones less or equal to j and larger than j. *)
  method split_vars vars j =
    match vars with
    | [] -> ([], [])
    | v :: vars' ->
      if v > j then
        ([], vars)
      else
        let vars1, vars2 = self#split_vars vars' j in
        (v :: vars1, vars2)
  *)

  (*
  (** Given vars of a nonterminal f and bindings (i, j, asX) with arguments that were substituting
      some of these vars, it returns tuples (i, j, vs, asX) with vs being all vars between i and j,
      inclusive. *)
  (* TODO why not do it in the first fun? *)
  method mk_binding_with_vars vars binding : (vars * hterms_id) binding =
    match binding with
    | [] -> []
    | (i, j, id) :: binding' ->
      let vars1, vars2 = self#split_vars vars j in
      if vars1 = [] then
        self#mk_binding_with_vars vars2 binding'
      else
        (* let vars1c = List.filter (fun i->not(List.mem i vars1)) (fromto i (j+1)) in *)
        (i, j, (vars1, id)) :: self#mk_binding_with_vars vars2 binding'
  *)

  (** Given a list of variables v1, v2, ... from a nonterminal f and bindings from application
      f as1 as2 ..., where asX translates to lists of terms through tab_id_terms, it returns all
      bindings (i, j, asY) such that i <= vK <= j for some K, i.e., that at least one of terms in
      tab_id_terms[asY] was substituted for some variable in nonterminal f. *)
  method filter_binding (vars : int list) (binding : hterms_id binding) : hterms_id binding =
    match binding with
    | [] -> []
    | (i, j, id) :: binding' ->
      match vars with
      | [] -> []
      | v::vars' ->
        if v < i then
          self#filter_binding vars' binding
        else if v <= j then
          (i, j, id) :: self#filter_binding vars' binding'
        else
          self#filter_binding vars binding'

  (** Computes all hterms identifiers present in a list of binding tuples, without duplicates. *)
  method ids_in_bindings bindings =
    let ids =
      List.fold_left (fun ids binding ->
          List.rev_append (List.map (fun (_, _, id) -> id) binding) ids
        ) [] bindings
    in
    sort_and_delete_duplicates ids

  (** Called for each term with term_id equal to id, that has free variables var, such that this
      term was an argument to a nonterminal. *)
  method mk_binding_depgraph_for_terms id vars =
    if SortedVars.is_empty vars then
      self#register_hterms_bindings id [[]]
    else
      let f = fst @@ SortedVars.hd vars in (* figure out in which nonterminal the term is defined using
                                              variable id *)
      let vars' = SortedVars.map snd vars in
      let bindings = nt_bindings.(f) in
      let bindings' =
        sort_and_delete_duplicates (* sorts and removes duplicates *)
          (List.rev_map (fun binding -> self#filter_binding vars' binding) bindings)
      in
      (*
      let bindings_with_vars =
        (* tuples (i, j, vs, as) where as was substituted for variables vs from vars' *)
        List.rev_map (self#mk_binding_with_vars vars') bindings'
      in
      *)
      let ids = self#ids_in_bindings bindings' in (* asX that are substituted into f's variables *)
      self#register_hterms_bindings id bindings'; (* register that term with given term id
                                                         had was present in some nonterminal and
                                                         given term sequences with id asX were
                                                         substituted for arguments i-j of this
                                                         nonterminal and specifically the list of
                                                         variables used was vsX *)
      List.iter (fun id1 -> self#register_hterms_where_hterms_flow id1 id) ids
  (* appending current hterm's id to hterms_where_hterms_flow[asX] if f was applied to asX making a
     substitution of some variable in hterm to asX *)
  
  method mk_binding_depgraph_for_nt (nt : int) : hterms_id binding list -> unit =
    (* when no vars are only in arguments of nonterminals and terminals *)
    (* if no variable occurs in the head position, we do not use binding information to compute
       the type of f *)
    (* TODO this is optional if Flags.eager is true
    if not (SortedVars.is_empty array_headvars.(f) && !Flags.eager) then
    *)
    List.iter (fun binding ->
        binding |> List.iter (
          (* TODO possible duplicates when a binding has two same hterms *)
          fun (_, _, id) -> self#register_nt_bindings_applied_to_hterms id nt binding
        )
      )

  (*
  method print_dep_nt_nt_lin =
    for i = 0 to Array.length nt_containing_nt_linearly - 1 do
      let nts = nt_containing_nt_linearly.(i) in
      if not (nts = SortedNTs.empty) then
        begin
          print_string @@ hg#nt_name i ^ " linearly occurs in ";
          SortedNTs.iter (fun j -> print_string @@ hg#nt_name j ^ ",") nts;
          print_string "\n"
        end
    done
  *)

  method compute_dependencies =
    for nt = 0 to hg#nt_count - 1 do
      array_headvars.(nt) <- hg#headvars_in_nt nt;
      self#mk_binding_depgraph_for_nt nt nt_bindings.(nt)
    done;
    (* make dependency nt --> id (which means "id depends on nt") *)
    for id' = 0 to hg#hterms_count - 1 do (* for each hterm *)
      let id = hg#hterms_count - 1 -id' in
      if hterms_are_arg.(id) then (* that had something applied to it *)
        let nts = hg#nts_in_hterms id in (* list of used nonterminals *)
        SortedNTs.iter (fun nt -> self#register_hterms_containing_nt nt id) nts
    done;
    for id = 0 to hg#hterms_count - 1 do
      if hterms_are_arg.(id) then
        let vars = hg#id2vars id in (* for each term with given id that was an argument
                                       to a nonterminal and had free variables vars *)
        self#mk_binding_depgraph_for_terms id vars
    done;
    (* make dependency nt1 --> nt2 (which means "nt2 depends on nt1") *)
    for nt1 = 0 to hg#nt_count - 1 do
      let nts1, nts2 = hg#nt_in_nt_with_linearity nt1 in
      SortedNTs.iter (fun nt2 -> self#register_dep_nt_nt nt2 nt1) nts2;
      (* TODO support for linearity
      if !Flags.incremental then
        SortedNTs.iter (fun nt2 -> self#register_dep_nt_nt_lin nt2 nt1) nts1
         else *)
      SortedNTs.iter (fun nt2 -> self#register_dep_nt_nt nt2 nt1) nts1
    done;
    print_verbose !Flags.verbose_preprocessing @@ lazy (
      self#string_of_hterms_bindings
      (* TODO print_nt_containing_nt ? *)
      (*
      self#print_dep_nt_nt_lin
      *)
    )

  initializer
    for i = 0 to hg#nt_count - 1 do
      variable_head_nodes.(i) <- Array.make (hg#nt_arity i) [] (* variable_head_nodes[nt_id][arg_id] = [] *)
    done;
    self#enqueue_hterm (HNT(0), []) (* enqueue first nonterminal with no args and first state *)
end
