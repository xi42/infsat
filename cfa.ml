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

module HTermSet = Set.Make(struct
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

  (** hterms_are_arg[id] contains a boolean whether hterms with given id can possibly be an
      argument to a nonterminal. It contains exactly the ids of hterms may be an argument to
      a nonterminal according to 0CFA, so there may be false positives. *)
  val mutable hterms_are_arg : bool array = [||]

  (** nt_bindings[nt] contains a list of bindings for nonterminal nt. Each binding corresponds
      to a possible application of nonterminal nt detected by 0CFA and is a list of tuples
      (i, j, id) stating that hterms identified by id are arguments from i-th to j-th (0-indexed)
      in given application.
      In short, this tells which lists hterms flow into which arguments of a nonterminal. *)
  val mutable nt_bindings : hterms_id binding list array = [||]

  (** var_bindings[nt][i] contains a list of hterms that may be i-th argument (0-indexed) to
      nonterminal nt according to 0CFA. *)
  val mutable var_bindings : hterm list array array = [||]

  (* identifier of [t1;...;tk] to a set of non-terminals
     whose variables may be bound to [t1;...;tk] *)
  (** tab_termid_nt[as] contains tuples (f, ts, qs) of nonterminals f, head terms ts, and states qs
      that were applied to list of terms tab_id_terms[as] and either Flags.eager is false or
      f has a head variable in its definition. *)
  (* TODO cleanup of docs *)
  val mutable tab_termid_nt : (int * hterms_id binding) list array = [||]

  (** variable_head_nodes[nt][i] is a list of processed hterms that have variable (nt, i) as
      head, i.e., i-th variable in definition of nonterminal nt. Internal for this module. *)
  (* TODO cleanup of docs *)
  val mutable variable_head_nodes : hterm list array array = [||]

  (** array_headvars[f] is a list of head variables in nonterminal's definition, i.e., variables
      that are applied to something. *)
  (* TODO cleanup of docs *)
  val mutable array_headvars : SortedVars.t array = [||]

  (* identifier of [t1;...;tk] --> identifiers of [s1;...;sl] 
     that depend on the value of [t1;...;tk];
     in other words, if id is mapped to [id1;...;idk] and
     the type of id has been updated, the types of id1,...,idk should
     be recomputed
     let tab_penv_binding = Hashtbl.create 10000 TODO remove old ver *)

  (** tab_penv_binding[as] contains a list of identifiers of lists of arguments (hterms) asX such
      that term tab_id_terms[asX] was applied with nonterminal containing tab_id_terms[as]
      substituting one of more variables present in snd tab_id_terms[as] (i.e., somewhere in the
      whole applicative term).
      In other words, these are the hterms that as is substituted into. *)
  (* TODO cleanup of docs (name it reverse_binding?) *)
  val mutable tab_penv_binding = [||]

  (** hterms_bindings[id] describes which hterms (sequences of terms) substitute which
      variables in hterms identified by id.
      Each binding is a list of tuples (i, j (v, h)) that describes that hterms identified by h
      were arguments from i-th to j-th (0-indexed) to a nonterminal nt in which hterms identified
      by id are defined, and that variables with indexes v (i.e., (nt, x) for all x in v) were
      substituted with hterms identified by h. *)
  val mutable hterms_bindings : (int list * hterms_id) binding list array = [||]

  (** array_dep_nt_termid[f] is a list of as ids such that tab_terms_id[as] expanded to applicative
      form (i.e., recursively) contains nonterminal f somewhere and this term was used as an
      argument to some nonterminal. *)
  (* TODO cleanup of docs *)
  val mutable array_dep_nt_termid = [||]

  (** array_dep_nt_nt[f] contains all nonterminals (int) that have f present in their body except
      for ones present in array_dep_nt_nt_lin[f]. *)
  (* TODO cleanup of docs *)
  val mutable array_dep_nt_nt : nts array = [||]

  (** If Flags.incremental is false then array_dep_nt_nt_lin[f] contains list of nonterminals g that
      have f present in their body exactly once at root or applied a number of times to a terminal,
      i.e., t1 .. (t2 .. (tN (f arg1 .. argK) ..) ..) .. for some terminals tX and terms argY. *)
  (* TODO cleanup of docs *)
  val mutable array_dep_nt_nt_lin : nts array = [||]

  (* --- access --- *)

  method hterms_are_arg (id : hterms_id) : bool =
    hterms_are_arg.(id)
  
  method has_head_vars (nt : nt_id) : bool =
    SortedVars.is_empty array_headvars.(nt)
  
  (* --- printing --- *)

  method print_binding (binding : hterms_id binding) =
    print_string @@ String.concat ", " @@ List.map (fun (i, j, id) ->
        string_of_int i ^ "-" ^ string_of_int j ^ " <- " ^ string_of_int id
      ) binding;
    print_string "\n"

  method print_binding_array =
    print_string @@ "bindings (nt --> one binding per line, comma-sep same-nt parts)\n" ^
                    "===============================================================\n\n";
    for nt = 0 to Array.length nt_bindings - 1 do (* TODO iter *)
      print_string @@ hg#nt_name nt ^ ":\n";
      List.iter self#print_binding (nt_bindings).(nt)
    done
    
  (* --- TODO split into categories --- *)

  method add_index rho i =
    match rho with
    | [] -> []
    | ids :: rho' -> (* for each args_id *)
      (* check how many terms are under args_id *)
      let n = List.length @@ hg#id2terms ids in
      let j = i+n in
      (i, j - 1, ids) :: self#add_index rho' j (* each termsid is converted to (first_term_number, last_term_number, termsid), like (0, 3, ...);(4, 5, ...);(6, 11, ...), i.e., start and end positions on a concatenated list of all terms *)

  method register_dep_termid_nt (id : hterms_id) (nt : nt_id) (termss : hterms_id binding) =
    let x = tab_termid_nt.(id) in
    (* TODO make sure there are no copies *)
    tab_termid_nt.(id) <- (nt, termss) :: x

  method lookup_dep_termid_nt id =
    tab_termid_nt.(id) 

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

  method print_hterm hterm =
    hg#print_hterm hterm

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
    | termsid::rho' ->
      let hterms = hg#id2hterms termsid in (* convert args_id back to a list of (H, [ID..]) *)
      let hterms' = index_list hterms in (* numbering these terms *)
      List.iter (* for each term register_binding_singlevar f global-numbering-id hterm *)
        (fun (j,hterm)-> self#register_binding_singlevar f (i+j) hterm)
        hterms';
      self#register_var_bindings f rho' (i+List.length hterms) (* recursively *)

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
        | HVar x ->
          (* check what hterms flow into x (these can also be variables) *)
          let x_hterms = self#lookup_binding_var x in
          (* substitute these hterms into x and enqueue resulting application *)
          List.iter (fun (h, x_args) ->
              self#enqueue_hterm (h, x_args @ h_args)
            ) x_hterms;
          self#register_variable_head_node x hterm
        | HNT nt ->
          (* Remember in nt_bindings that there was an application f h_args. Also remember
             that h_args were being used as an argument to a nonterminal in hterms_are_arg. *)
          self#register_binding nt h_args;
          (* Enqueue the body hterm, ignoring all arguments. Note that arguments are not enqueued.
             If the arguments don't have kind O, they can be passed as arguments again, or used
             as variable head, which finds the original terms. *)
          self#enqueue_hterm @@ hg#nt_body nt
      end

  (** Expand hterms in queue until it's empty. *)
  method expand : unit =
    match self#dequeue_hterm with
    | None ->
      if !Flags.debugging then
        begin
          self#print_binding_array;
          print_string @@ "\nSize of abstract control flow graph: " ^
                          string_of_int (HTermSet.cardinal visited_nodes) ^ "\n"
        end
    | Some hterm ->
      self#process_hterm hterm;
      self#expand

  (** Appends hterm id2 to id1's list of tab_penv_binding. *)
  method register_dep_penv_binding id1 id2 =
    let ids = tab_penv_binding.(id1) in
    tab_penv_binding.(id1) <-id2::ids

  method lookup_dep_id id =
    tab_penv_binding.(id)

  method register_hterms_bindings id bindings =
    hterms_bindings.(id) <- bindings (* only place with actual modification *)

  method print_mask mask =
    print_string "[";
    List.iter (fun i -> print_string @@ string_of_int i ^ ",") mask;
    print_string "]"

  method print_binding_with_mask binding =
    List.iter (fun (i, j, (mask,id1)) ->
        print_string @@ "(" ^ string_of_int i ^ "," ^ string_of_int j ^ ",";
        self#print_mask mask;
        print_string @@ ", " ^ string_of_int id1 ^ "), "
      ) binding; 
    print_string "\n"

  method print_hterms_bindings =
    print_string "dependency info. (id --> [(i,j,id1);...])\n";
    for id=0 to Array.length hterms_bindings - 1 do
      if hterms_are_arg.(id) then
        begin
          print_int id; print_string ":\n";
          List.iter self#print_binding_with_mask hterms_bindings.(id)
        end
    done

  method lookup_dep_id_envs id =
    hterms_bindings.(id)

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

  (** Given vars of a nonterminal f and bindings (i, j, asX) with arguments that were substituting
      some of these vars, it returns tuples (i, j, vs, asX) with vs being all vars between i and j,
      inclusive. *)
  (* TODO why not do it in the first fun? *)
  method mk_binding_with_mask vars binding: (int list * hterms_id) binding =
    match binding with
    | [] -> []
    | (i, j, id) :: binding' ->
      let vars1, vars2 = self#split_vars vars j in
      if vars1 = [] then
        self#mk_binding_with_mask vars2 binding'
      else
        (* let vars1c = List.filter (fun i->not(List.mem i vars1)) (fromto i (j+1)) in *)
        (i, j, (vars1, id)) :: self#mk_binding_with_mask vars2 binding'

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
    delete_duplication_unsorted ids

  (** Called for each term with term_id equal to id, that has free variables var, such that this
      term was an argument to a nonterminal. *)
  method mk_binding_depgraph_for_terms id vars =
    if vars = SortedVars.empty then
      self#register_hterms_bindings id [[]]
    else
      let f = fst @@ SortedVars.hd vars in (* figure out in which nonterminal the term is defined using
                                          variable id *)
      let vars' = SortedVars.map snd vars in (* get indexes of variables in term f *)
      let bindings = nt_bindings.(f) in
      let bindings' =
        delete_duplication_unsorted (* sorts and removes duplicates *)
          (List.rev_map (fun binding -> self#filter_binding vars' binding) bindings)
      in
      let bindings_with_mask =
        (* tuples (i, j, vs, as) where as was substituted for variables vs from vars' *)
        List.rev_map (self#mk_binding_with_mask vars') bindings'
      in
      let ids = self#ids_in_bindings bindings' in (* asX that are substituted into f's variables *)
      self#register_hterms_bindings id bindings_with_mask; (* register that term with given term id
                                                         had was present in some nonterminal and
                                                         given term sequences with id asX were
                                                         substituted for arguments i-j of this
                                                         nonterminal and specifically the list of
                                                         variables used was vsX *)
      List.iter (fun id1 -> self#register_dep_penv_binding id1 id) ids
  (* appending current hterm's id to tab_penv_binding[asX] if f was applied to asX making a
     substitution of some variable in hterm to asX *)

  method mk_binding_depgraph_for_termss (f : int) (termss : hterms_id binding) =
    List.iter (fun (_, _, id) -> self#register_dep_termid_nt id f termss) termss (* for each term to which f was applied *)

  method mk_binding_depgraph_for_nt (f : int) (termsss : hterms_id binding list) =
    (* when no vars are only in arguments of nonterminals and terminals *)
    (* if no variable occurs in the head position, we do not use binding information to compute
       the type of f *)
    if not (array_headvars.(f) = SortedVars.empty && !Flags.eager) then
      List.iter (self#mk_binding_depgraph_for_termss f) termsss
        
  method print_dep_nt_nt_lin =
    for i = 0 to Array.length array_dep_nt_nt_lin - 1 do
      let nts = array_dep_nt_nt_lin.(i) in
      if not (nts = SortedNTs.empty) then
        begin
          print_string @@ hg#nt_name i ^ " linearly occurs in ";
          SortedNTs.iter (fun j -> print_string @@ hg#nt_name j ^ ",") nts;
          print_string "\n"
        end
    done

  method init_array_dep_nt_termid =
    let n = Array.length nt_bindings in (* number of nonterminals *)
    array_dep_nt_termid <- Array.make n [] (* a list for each nonterminal *)

  method init_array_dep_nt_nt =
    let n = Array.length nt_bindings in
    array_dep_nt_nt <- Array.make n SortedNTs.empty;
    array_dep_nt_nt_lin <- Array.make n SortedNTs.empty

  (* nt occurs in the term id *)
  method register_dep_nt_termid nt id =
    let ids = array_dep_nt_termid.(nt) in
    (* this function can never be called with the same (nt,id) pair *)
    let ids' = id :: ids (*merge_and_unify compare [id] ids*) in
    array_dep_nt_termid.(nt) <- ids'

  method register_dep_nt_nt nt1 nt2 =
    let nts = array_dep_nt_nt.(nt1) in
    let nts' = SortedNTs.merge (SortedNTs.singleton nt2) nts in
    array_dep_nt_nt.(nt1) <- nts'

  method register_dep_nt_nt_lin nt1 nt2 =
    let nts = array_dep_nt_nt_lin.(nt1) in
    let nts' = SortedNTs.merge (SortedNTs.singleton nt2) nts in
    array_dep_nt_nt_lin.(nt1) <- nts'

  method lookup_dep_nt_termid nt =
    array_dep_nt_termid.(nt)

  method lookup_dep_nt_nt nt =
    array_dep_nt_nt.(nt)

  method lookup_dep_nt_nt_lin nt =
    array_dep_nt_nt_lin.(nt)

  method mk_binding_depgraph =
    tab_termid_nt <- Array.make hg#hterms_count []; (* array of lists for each head term (hterm) *)
    hterms_bindings <- Array.make hg#hterms_count [];
    tab_penv_binding <- Array.make hg#hterms_count [];
    let n = Array.length nt_bindings in (* number of nonterminals *)
    array_headvars <- Array.make n SortedVars.empty; (* array of lists for each nonterminal *)
    for nt = 0 to n - 1 do
      array_headvars.(nt) <- hg#headvars_in_nt nt;
      self#mk_binding_depgraph_for_nt nt nt_bindings.(nt)
    done;
    (* make dependency nt --> id (which means "id depends on nt") *)
    self#init_array_dep_nt_termid;
    for id' = 0 to hg#hterms_count - 1 do (* for each hterm *)
      let id = hg#hterms_count - 1 -id' in
      if hterms_are_arg.(id) then (* that had something applied to it *)
        let nts = hg#nts_in_hterm id in (* list of used nonterminals *)
        SortedNTs.iter (fun nt -> self#register_dep_nt_termid nt id) nts
    done;
    for id = 0 to hg#hterms_count - 1 do
      if hterms_are_arg.(id) then
        let vars = hg#id2vars id in (* for each term with given id that was an argument
                                       to a nonterminal and had free variables vars *)
        self#mk_binding_depgraph_for_terms id vars
    done;
    (* make dependency nt1 --> nt2 (which means "nt2 depends on nt1") *)
    self#init_array_dep_nt_nt;
    let n = hg#nt_count in
    for nt1 = 0 to n - 1 do
      let nts1, nts2 = hg#nt_in_nt_with_linearity nt1 in
      SortedNTs.iter (fun nt2 -> self#register_dep_nt_nt nt2 nt1) nts2;
      if !Flags.incremental then
        SortedNTs.iter (fun nt2 -> self#register_dep_nt_nt_lin nt2 nt1) nts1
      else 
        SortedNTs.iter (fun nt2 -> self#register_dep_nt_nt nt2 nt1) nts1
    done;
    if !Flags.debugging then
      begin
        self#print_hterms_bindings;
        print_string "\n";
        self#print_dep_nt_nt_lin
      end

  initializer
    let num_of_nts = hg#nt_count in
    hterms_are_arg <- Array.make hg#hterms_count false;
    nt_bindings <- Array.make num_of_nts []; (* nt_bindings[nt_id] = [] *)
    var_bindings <- Array.make num_of_nts [||]; (* var_bindings[nt_id][arg_id] = [] *)
    for i = 0 to num_of_nts - 1 do
      var_bindings.(i) <- Array.make (hg#nt_arity i) []
    done;
    variable_head_nodes <- Array.make num_of_nts [||];
    for i = 0 to num_of_nts - 1 do
      variable_head_nodes.(i) <- Array.make (hg#nt_arity i) [] (* variable_head_nodes[nt_id][arg_id] = [] *)
    done;
    self#enqueue_hterm (HNT(0), []) (* enqueue first nonterminal with no args and first state *)
end
