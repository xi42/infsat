(** Control flow analysis module implementing 0CFA. *)

open Grammar
open GrammarCommon
open HGrammar
open Utilities

(* --- types --- *)

type node = hterm
type 'a binding_elt = int * int * 'a
type 'a binding = 'a binding_elt list

(* hterm -> ref (hterm, qs) *)
module HType = struct
  type t = hterm
  let equal i j = i=j
  let hash = Hashtbl.hash_param 100 100
end

module HTermHashtbl = Hashtbl.Make(HType)

module SortedHTermsIds = SortedList.Make(struct
    type t = hterms_id
    let compare = Pervasives.compare
  end)

(* TODO remove dependency on grammar *)
class cfa (grammar : grammar) (hgrammar : hgrammar) = object(self)
  (* --- registers --- *)

  (* necessary tables:
     - map from hterm to node

     - binding information, which maps 
     each variable x to a binding list of the form (x1,...,xk)|-> {(t11,...,t1k),...,(tj1,...,tjk)}
     each non-terminal to a binding list of the form (x1,...,xk)|-> {(t11,...,t1k),...,(tj1,...,tjk)}
     (the former can be obtained from the latter and the table below)
     Should the binding also contain information about which terms share the environment
     (so, [[~t11];...;[~tik]] instead of (t11,...,t1k))

     - map from each subterm to the non-terminal of the rule containing the subterm?
     - map from each variable to a pair consisting of non-terminal and index?
     (to make it easy to find binding)
  *)

  (** termid_isarg[i] contains a boolean whether tab_id_terms[i] was ever used as an argument when
      expanding terms in expand, i.e., if it was a used argument to a nonterminal. Filled during
      expansion. *)
  val mutable termid_isarg : bool array = [||]

  (** binding_array_nt[f] contains a list of bindings for nonterminal f (int), i.e., a list of
      tuples (ts, qs) such that ts are terms that f was applied to under states qs, where qs is a
      reference to a list of states (ints), and ts is a list of tuples (i, j, asW) such that
      nonterminal f was applied to arguments
      f a11 a12 .. a1X a21 .. a2Y .. aP1 .. aPZ
      where tab_id_terms[asW] translates to a list of terms aW1 .. aWR for some R, and term aW1 was
      i-th on the list of arguments and term aWR was j-th on the list of arguments applied to f.
      In short, this is used to tell what terms where which arguments of f under what states.
      Internal for this module, filled during expansion. *)
  val mutable binding_array_nt : hterms_id binding list array = [||]

  (** binding_array_var[f][i] contains terms in head form (h, [ID..]) that were i-th argument
      (0-indexed) to nonterminal f (int). *)
  val mutable binding_array_var : hterm list array array = [||]

  (* identifier of [t1;...;tk] to a set of non-terminals
     whose variables may be bound to [t1;...;tk] *)
  (** tab_termid_nt[as] contains tuples (f, ts, qs) of nonterminals f, head terms ts, and states qs
      that were applied to list of terms tab_id_terms[as] and either Flags.eager is false or
      f has a head variable in its definition. *)
  val mutable tab_termid_nt : (int * hterms_id binding) list array = [| |]

  (** variable_head_nodes[f][i] is a list of processed nodes that have variable (f,i) as head,
      i.e., i-th variable in definition of nonterminal f. Internal for this module. *)
  val mutable variable_head_nodes : node ref list array array = [||]

  (** nodetab[hterm] = (hterm, qs), where qs is a list of states under which term hterm (in head
      form) was processed. *)
  (* TODO change this to set *)
  val mutable nodetab = HTermHashtbl.create 100000

  (** Queue of nodes to process as a list of (t, qs), where t is a term in head form (H, [ID..]), and
      qs is a list of states (ints). The queue eventually processes all (t, qs) combinations that are
      possible during reducing the starting symbol, and more (some unnecessary terms may be analyzed,
      such as in K t id, and some unnecessary states may be analyzed). *)
  val mutable nodequeue : node list = []

  (** array_headvars[f] is a list of head variables in nonterminal's definition, i.e., variables
      that are applied to something. *)
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
  val mutable tab_penv_binding = [| |]

  (* identifier of [t1;...;tk] ---> a list of [(i,j,id1);...]
     [(i1,j1,id1);...;(ik,j1,idk)] being an element of the list
     means that the i_x-th to j_x-th free variables in [t1;...;tk]
     may be bound to the terms represented by id_x 
     let tab_binding_env: (termid, (int*int*termid) list list) Hashtbl.t = Hashtbl.create 10000
  *)

  (** tab_binding_env[as] describes which hterms (sequences of terms) substitute which variables in
      term with id as.
      This as hterm was present in some nonterminal with variables numbered form 0 to K.
      Specifically, it is a list of list of tuples (i, j, vs, as'), where each list of tuples is
      one application, and in this application arguments i-j (sub-interval of 0-K) were substituted
      (specifically variables vs (list of ints from interval i-j)) with hterms with id as'.
      Intuitively, this means that as' was substituted for a variable inside as. *)
  val mutable tab_binding_env = [||]

  (** array_dep_nt_termid[f] is a list of as ids such that tab_terms_id[as] expanded to applicative
      form (i.e., recursively) contains nonterminal f somewhere and this term was used as an
      argument to some nonterminal. *)
  val mutable array_dep_nt_termid = [||]

  (** array_dep_nt_nt[f] contains all nonterminals (int) that have f present in their body except
      for ones present in array_dep_nt_nt_lin[f]. *)
  val mutable array_dep_nt_nt : SortedNTs.t array = [||]

  (** If Flags.incremental is false then array_dep_nt_nt_lin[f] contains list of nonterminals g that
      have f present in their body exactly once at root or applied a number of times to a terminal,
      i.e., t1 .. (t2 .. (tN (f arg1 .. argK) ..) ..) .. for some terminals tX and terms argY. *)
  val mutable array_dep_nt_nt_lin : SortedNTs.t array = [||]

  (* --- logic --- *)

  (* --- ? --- *)

  method print_binding (binding : hterms_id binding) =
    print_string @@ String.concat ", " @@ List.map (fun (i, j, id) ->
        string_of_int i ^ "-" ^ string_of_int j ^ " <- " ^ string_of_int id
      ) binding;
    print_string "\n"

  method print_binding_array =
    print_string "bindings (nt --> bindings list)\n\n";
    for nt = 0 to Array.length binding_array_nt - 1 do (* TODO iter *)
      print_string ((hgrammar#nt_name nt)^":\n");
      List.iter self#print_binding (binding_array_nt).(nt)
    done

  method add_index rho i =
    match rho with
    | [] -> []
    | termsid::rho' -> (* for each args_id *)
      let n = List.length (hgrammar#id2terms termsid) in (* check how many terms are under args_id *)
      (*       if n<9 then *)
      let j = i+n in
      (i,j-1,termsid)::(self#add_index rho' j) (* each termsid is converted to (first_term_number, last_term_number, termsid), like (0, 3, ...);(4, 5, ...);(6, 11, ...), i.e., start and end positions on a concatenated list of all terms *)

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


  method register_variable_head_node v (noderef: node ref) =
    let (nt, i) = v in
    let a = variable_head_nodes.(nt) in
    a.(i) <- noderef :: a.(i)

  method lookup_variable_head_node (nt,i) =
    variable_head_nodes.(nt).(i)

  (** Prepends term to list terms if it is not already there. Returns tuple of resulting list and
      boolean whether it was prepended to list. *)
  method insert_var_binding (term : 'a) (terms : 'a list) : 'a list * bool =
    if List.mem term terms then
      (terms, false)
    else
      (term :: terms, true)

  method print_node hterm =
    hgrammar#print_hterm hterm

  method clear_nodequeue =
    nodequeue <- []

  method enqueue_node node =
    nodequeue <- node::nodequeue

  method dequeue_node =
    match nodequeue with
    | [] -> None
    | x::q ->
      nodequeue <- q;
      Some(x)

  method enqueue_nodes nodes =
    List.iter self#enqueue_node nodes

  method expand_varheadnode term (node: node ref) =
    let hterm = !node in
    let h, termss = hterm in
    match h with
    | HVar x ->
      let (h', terms) = term in
      self#enqueue_node (h', terms@termss)
    | _ -> assert false

  (** Iterates (expand_varheadnode term) over everything in variable_head_nodes[nt_id][arg_id] *)
  method expand_varheadnodes f i term =
    let nodes = self#lookup_variable_head_node (f, i) in
    List.iter (self#expand_varheadnode term) nodes

  (** Called when term was i-th argument in a call f arg1 arg2 ...
      It makes sure that binding_array_var[f][i] contains terms (H, [ID..]) that were
      i-th argument to nonterminal f, and calls expand_varheadnodes f i term when it was the first
      time adding it to binding_array_var. *)
  method register_binding_singlevar nt i term =
    let tab = binding_array_var.(nt) in (* binding_array_var[nt_id][arg_id] = [...] *)
    let (binds, changed) = self#insert_var_binding term tab.(i) in (* making sure term is in binding_array_var[nt_id][arg_id] *)
    if changed then (* if it was added just now *)
      begin
        tab.(i) <- binds; (* persist the addition *)
        self#expand_varheadnodes nt i term
      end

  method lookup_binding_var (nt, i) = 
    binding_array_var.(nt).(i)

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
      let hterms = hgrammar#id2hterms termsid in (* convert args_id back to a list of (H, [ID..]) *)
      let hterms' = index_list hterms in (* numbering these terms *)
      List.iter (* for each term register_binding_singlevar f global-numbering-id hterm *)
        (fun (j,hterm)-> self#register_binding_singlevar f (i+j) hterm)
        hterms';
      self#register_var_bindings f rho' (i+List.length hterms) (* recursively *)

  (** Register information that there was a call f args, i.e., save this as a binding in
      binding_array_nt and register in termid_isarg that args were an argument to nonterminal f. *)
  method register_binding (nt : int) (args : int list) =
    (* binding_array_nt[nt] contains a list of
       ((number of first term in app, number of last term in app, args_id for first bundle of terms in app)::..., states under which visited) *)
    List.iter (fun id -> termid_isarg.(id) <- true) args;
    binding_array_nt.(nt) <- (self#insert_nt_binding args binding_array_nt.(nt));
    self#register_var_bindings nt args 0

  method lookup_bindings_for_nt nt =
    binding_array_nt.(nt)

  (** Registering in nodetab that a new hterm is being processed. *)
  method register_newnode hterm = 
    if HTermHashtbl.mem nodetab hterm then assert false;
    let node = ref hterm in
    HTermHashtbl.add nodetab hterm node;
    node

  method lookup_nodetab hterm = 
    try
      Some(HTermHashtbl.find nodetab hterm)
    with Not_found -> None

  (** Enqueueing all argument hterms. The terminal does not matter. *)
  method expand_terminal termss =
    List.iter (fun hterm -> self#enqueue_node hterm) termss

  (* TODO unused
  (** Returns size of term as number of non-application terms on left-hand size of application (not number of terminals/nonterminals) *)
  method size_of_appterm t =
    match t with
    | App (t1, t2) ->
      ( match t1 with
          App(_, _) -> self#size_of_appterm t1 + self#size_of_appterm t2
        | _ -> 1 + self#size_of_appterm t2)
    | _ -> 0

  method size_of_rules r =
    Array.fold_left (fun s (_, t) -> s + self#size_of_appterm t) 0 r
  *)

  (** Processing hterms. *)
  method process_node hterm = 
    match self#lookup_nodetab hterm with
    | Some(_) -> (* hterm has been processed before *)
      ()
    | None -> (* the hterm has not been processed yet *)
      let (h, h_args) = hterm in
      (* saving that the hterm is already processed *)
      let node = self#register_newnode hterm in
      (* expanding the calls to see what hterms go in what variables *)
      match h with
      | HT _ ->
        (* decoding arguments as hterm ids into hterms *)
        let (_, termss) = hgrammar#decompose_hterm hterm in
        (* ignore the terminal and go deeper *)
        self#expand_terminal termss
      | HVar(x) ->
        (* check what hterms flow into x (these can also be variables) *)
        let x_hterms = self#lookup_binding_var x in
        (* substitute these hterms into x and enqueue resulting application *)
        List.iter (fun (h, x_args) -> self#enqueue_node (h, x_args@h_args)) x_hterms;
        self#register_variable_head_node x node
      | HNT(f) ->
        (* Remember in binding_array_nt that there was an application f h_args. Also remember
           that h_args were being used as an argument to a nonterminal in termid_isarg. *)
        self#register_binding f h_args;
        (* Enqueue the body hterm, ignoring all arguments. Note that arguments are not enqueued.
           If the arguments don't have kind O, they can be passed as arguments again, or used
           as variable head, which finds the original terms. *)
        self#enqueue_node (hgrammar#nt_body f)

  (** Expand nodes in queue until it's empty. *)
  method expand : unit =
    match self#dequeue_node with
    | None ->
      if !Flags.debugging then
        begin
          self#print_binding_array;
          print_string ("\nSize of abstract control flow graph: " ^ string_of_int (HTermHashtbl.length nodetab) ^ "\n")
        end
    | Some hterm ->
      self#process_node hterm;
      self#expand

  (** Appends hterm id2 to id1's list of tab_penv_binding. *)
  method register_dep_penv_binding id1 id2 =
    let ids = tab_penv_binding.(id1) in
    tab_penv_binding.(id1) <-id2::ids

  method lookup_dep_id id =
    tab_penv_binding.(id)

  method register_dep_binding_env id bindings =
    tab_binding_env.(id) <- bindings (* only place with actual modification *)

  method print_mask mask =
    print_string "[";
    List.iter(fun i-> print_string((string_of_int i)^",")) mask;
    print_string "]"

  method print_binding_with_mask binding =
    List.iter (fun (i,j,mask,id1) ->
        print_string ("(" ^ string_of_int i ^ "," ^ string_of_int j ^ ",");
        self#print_mask mask;
        print_string (", " ^ string_of_int id1 ^ "), "))
      binding; 
    print_string "\n"

  method print_tab_binding_env =
    print_string "dependency info. (id --> [(i,j,id1);...])\n";
    for id=0 to Array.length tab_binding_env - 1 do
      if termid_isarg.(id) then
        begin
          print_int id; print_string ":\n";
          List.iter self#print_binding_with_mask tab_binding_env.(id)
        end
    done

  method lookup_dep_id_envs id =
    tab_binding_env.(id)

  (** Splits a list of vars to ones less or equal to j and larger than j. *)
  method split_vars vars j =
    match vars with
    | [] -> ([], [])
    | v::vars' ->
      if v>j then
        ([], vars)
      else
        let vars1, vars2 = self#split_vars vars' j in
  (v :: vars1, vars2)

  (** Given vars of a nonterminal f and bindings (i, j, asX) with arguments that were substituting
      some of these vars, it returns tuples (i, j, vs, asX) with vs being all vars between i and j,
      inclusive. *)
  (* TODO why not do it in the first fun? *)
  method mk_binding_with_mask vars binding: (int * int * int list * int) list =
    match binding with
    | [] -> []
    | (i, j, id)::binding' ->
      let (vars1,vars2) = self#split_vars vars j in
      if vars1=[] then
  self#mk_binding_with_mask vars2 binding'
      else
        (* let vars1c = List.filter (fun i->not(List.mem i vars1)) (fromto i (j+1)) in *)
        (i, j, vars1, id) :: (self#mk_binding_with_mask vars2 binding')

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
          (i, j, id) :: (self#filter_binding vars' binding')
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
      self#register_dep_binding_env id [[]]
    else
      let f = fst @@ SortedVars.hd vars in (* figure out in which nonterminal the term is defined using
                                          variable id *)
      let vars' = SortedVars.map snd vars in (* get indexes of variables in term f *)
      let bindings = binding_array_nt.(f) in
      let bindings' =
        delete_duplication_unsorted (* sorts and removes duplicates *)
          (List.rev_map (fun binding -> self#filter_binding vars' binding) bindings)
(*
     List.fold_left
       (fun bindings1 (binding,_) ->
         let b = filter_binding vars' binding in
   if List.mem b bindings1 then bindings1
else b::bindings1)
       [] bindings
*)       
      in
      let bindings_with_mask =
        (* tuples (i, j, vs, as) where as was substituted for variables vs from vars' *)
        List.rev_map (self#mk_binding_with_mask vars') bindings'
      in
      let ids = self#ids_in_bindings bindings' in (* asX that are substituted into f's variables *)
      (*   
   let bindings_with_mask =
    List.fold_left
      (fun bindmasks (binding,_) ->
        let b = mk_binding_with_mask vars' binding in
if List.mem b bindmasks then bindmasks
else b::bindmasks)
      [] bindings
   in
*)
      self#register_dep_binding_env id bindings_with_mask; (* register that term with given term id
                                                         had was present in some nonterminal and
                                                         given term sequences with id asX were
                                                         substituted for arguments i-j of this
                                                         nonterminal and specifically the list of
                                                         variables used was vsX *)
      List.iter (fun id1 -> self#register_dep_penv_binding id1 id) ids
  (* appending current hterm's id to tab_penv_binding[asX] if f was applied to asX making a
     substitution of some variable in hterm to asX *)
(*
     List.iter (fun env-> register_dep_env_binding env id)  bindings_with_mask
*)
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
          print_string @@ hgrammar#nt_name i ^ " linearly occurs in ";
          SortedNTs.iter (fun j -> print_string @@ hgrammar#nt_name j ^ ",") nts;
          print_string "\n"
        end
    done

  method init_array_dep_nt_termid =
    let n = Array.length binding_array_nt in (* number of nonterminals *)
    array_dep_nt_termid <- Array.make n [] (* a list for each nonterminal *)

  method init_array_dep_nt_nt =
    let n = Array.length binding_array_nt in
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

  (** List of all nonterminals in terms without duplicates. *)
  method nt_in_terms (terms : term list) : SortedNTs.t =
    match terms with
    | [] -> SortedNTs.empty
    | t :: terms' -> SortedNTs.merge (Grammar.nt_in_term t) (self#nt_in_terms terms')

  method merge_nts_lin (nts1, nts2) (nts3, nts4) =
    let nts11, nts12 =
      SortedNTs.partition (fun f -> SortedNTs.mem f nts3 || SortedNTs.mem f nts4) nts1 in
    let nts31, nts32 =
      SortedNTs.partition (fun f -> SortedNTs.mem f nts1 || SortedNTs.mem f nts2) nts3 in
    (SortedNTs.merge nts12 nts32,
     SortedNTs.merge nts11
       (SortedNTs.merge nts31 
          (SortedNTs.merge nts2 nts4)))

  (** Takes all nonterminals L in position at either term = L1, L1 arg1 .. argK, or
      t1 (.. (tN (L1 ..) ..) .., where tX are terminals, where L additionally satisfy the condition
      that they appear exactly once in the term. It returns ([L1; ..], [N1; ..]), where NX are
      other nonterminals present in the term.
      Intuitively, it returns on the left all nonterminals that have have a sequence (possibly
      empty) of terminals applied to them and appear exactly once in the term, and the rest of
      nonterminals on the right. *)
  method nt_in_term_with_linearity (term : term) : SortedNTs.t * SortedNTs.t =
    match term with
    | T _ | Var _ -> (SortedNTs.empty, SortedNTs.empty)
    | NT f -> (SortedNTs.singleton f, SortedNTs.empty)
    | App _ ->
      let (h,terms) = Grammar.decompose_term term in
      match h with
      | NT(f) -> let nts = self#nt_in_terms terms in
        if SortedNTs.mem f nts then
          (SortedNTs.empty, nts) (* if head nt used twice *)
        else
          (SortedNTs.singleton f, nts) (* if head nt used once *)
      | Var _ -> (SortedNTs.empty, self#nt_in_terms terms)
      | T _ ->
        (* c has no children. a has a single child, so it is linear. b has two children, but only
           one at a time is used. Even if we do b (N ..) (N ..) that yield different types, only
           one N is used as long as there is no other N present. Therefore, b is also linear. *)
        self#nt_in_terms_with_linearity terms 0 (SortedNTs.empty, SortedNTs.empty)
      | _ -> assert false

  method nt_in_terms_with_linearity terms i (nts1, nts2) : SortedNTs.t * SortedNTs.t =
    match terms with (* iteration over terms and linearity info simultaneously *)
    | [] -> (nts1, nts2) 
    | t :: terms' ->
      let (nts1', nts2') = self#nt_in_term_with_linearity t (* recursively *) in
      let (nts1'', nts2'') = self#merge_nts_lin (nts1', nts2') (nts1, nts2) in
      self#nt_in_terms_with_linearity terms' (i + 1) (nts1'', nts2'')

  method mk_binding_depgraph =
    tab_termid_nt <- Array.make hgrammar#hterms_count []; (* array of lists for each head term (hterm) *)
    tab_binding_env <- Array.make hgrammar#hterms_count [];
    tab_penv_binding <- Array.make hgrammar#hterms_count [];
    let n = Array.length binding_array_nt in (* number of nonterminals *)
    array_headvars <- Array.make n SortedVars.empty; (* array of lists for each nonterminal *)
    for f = 0 to n - 1 do
      array_headvars.(f) <- (let (_, t)= grammar#rule f in (* applicative rule definition *)
                                headvars_in_term t);
      self#mk_binding_depgraph_for_nt f binding_array_nt.(f)
    done;
    (* make dependency nt --> id (which means "id depends on nt") *)
    self#init_array_dep_nt_termid;
    for id' = 0 to hgrammar#hterms_count - 1 do (* for each hterm *)
      let id = hgrammar#hterms_count - 1 -id' in
      if termid_isarg.(id) then (* that had something applied to it *)
        let terms = hgrammar#id2terms id in (* and is in applicative form list of terms,
                                                          and has variables vars *)
        let nts = self#nt_in_terms terms in (* list of used nonterminals *)
        SortedNTs.iter (fun nt -> self#register_dep_nt_termid nt id) nts
    done;
    for id = 0 to hgrammar#hterms_count - 1 do
      if termid_isarg.(id) then
        let vars = hgrammar#id2vars id in (* for each term with given id that was an argument
                                                      to a nonterminal and had free variables vars *)
        self#mk_binding_depgraph_for_terms id vars
    done;
    (* make dependency nt1 --> nt2 (which means "nt2 depends on nt1") *)
    self#init_array_dep_nt_nt;
    let n = hgrammar#nt_count in
    for i = 0 to n - 1 do
      let (_, t) = grammar#rule i in
      let (nts1, nts2) = self#nt_in_term_with_linearity t in
      SortedNTs.iter (fun nt-> self#register_dep_nt_nt nt i) nts2;
      if !Flags.incremental then
        SortedNTs.iter (fun nt-> self#register_dep_nt_nt_lin nt i) nts1
      else 
        SortedNTs.iter (fun nt-> self#register_dep_nt_nt nt i) nts1
    done;
    if !Flags.debugging then
      begin
        self#print_tab_binding_env;
        print_string "\n";
        self#print_dep_nt_nt_lin
      end

  initializer
    HTermHashtbl.clear nodetab;
    self#clear_nodequeue;
    let num_of_nts = hgrammar#nt_count in
    termid_isarg <- Array.make grammar#size false;
    binding_array_nt <- Array.make num_of_nts []; (* binding_array_nt[nt_id] = [] *)
    binding_array_var <- Array.make num_of_nts [||]; (* binding_array_var[nt_id][arg_id] = [] *)
    for i = 0 to num_of_nts - 1 do
      binding_array_var.(i) <- Array.make (hgrammar#nt_arity i) []
    done;
    variable_head_nodes <- Array.make num_of_nts [||];
    for i = 0 to num_of_nts - 1 do
      variable_head_nodes.(i) <- Array.make (hgrammar#nt_arity i) [] (* variable_head_nodes[nt_id][arg_id] = [] *)
    done;
    self#enqueue_node (HNT(0), []) (* enqueue first nonterminal with no args and first state *)
end
