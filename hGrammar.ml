open Grammar
open GrammarCommon

(** Identifier of a sequence of hterms (terms in head form) that is an argument to some head term.
    Terms under one hterms_id are defined in one nonterminal or do not contain a variable. *)
type hterms_id = int
(** Head of a term in head form. *)
type head = HT of terminal | HNT of nt_id | HVar of var_id
(** Hterm is a term in head form. It consists of a head and identifiers of sequences of hterms
    that are its arguments. If hterm is (h, [a1;..;aK]) and aX represents a sequence of terms
    [tX1;..;tXl] for some l then the whole hterm represents an application
    h t11 .. t1A t21 .. t2B .. tK1 .. tKZ.
    Note that nonterminal bodies have K <= 1 and only bindings may have more. *)
type hterm = head * hterms_id list

class hgrammar (grammar : grammar) = object(self)
  (** Mapping from int ids to lists of terms. when tab_id_terms[i] = (hterms, terms, vars), then
      hterms is a list of terms [a1; a2; ..; aN], each in head form (h, [i1; i2; ..; iM]).
      h is a terminal, nonterminal, or a variable. iX points at tab_id_terms[iX]. This represents
      an applicative term
      h a11 a12 ... a1K a21 ... aM1 ... aMR
      terms are hterms in the original tree representation, and vars is a list of all free
      variables in terms. Variables are represented as integer tuples (X, Y) for Y-th argument
      (0-indexed) of X-th nonterminal (0-indexed).
      Note that two terms with variables that are used in two different nonterminal definitions
      will have different ids, because variables are tuples (nt_id, var_id) that are disjoint for
      different nonterminal bodies.
      More is allocated than needed here. *)
  val hterms_data : (hterm list * Grammar.term list * vars * nt_id option) array =
    Array.make grammar#size ([], [], SortedVars.empty, None)

  (** Reverse of fst hterms_data, i.e., hterms_data[tab_terms_id[hterms]] = (hterms, _, _). *)
  val tab_terms_id = Hashtbl.create 100000
  
  (** After the nonterminals are numbered, this is a map from nonterminals' ids to their bodies in
      head form. Bodies in head form are tuples (h, [as1; as2; ..]), where asX are integers that
      are mapped to lists of terms in head form, i.e., as1 = [a11; a12; ...]. The original tuple
      then represents
      h a11 a12 ... a1n a21 a22 ... a2m ...
      Mappings from asX to lists are in hterms_data. *)
  val nt_bodies : hterm array = Array.make grammar#nt_count (HNT (-1), [])

  (** Increasing counter for fresh identifiers for hterms (all terms and subterms in head form). *)
  val mutable next_hterms_id : int = 0

  (* --- access --- *)

  method start_nt : nt_id = 0
  
  method nt_count : int = Array.length nt_bodies

  method nt_arity (nt : nt_id) : int = grammar#arity_of_nt nt

  method nt_name (nt : nt_id) : string = grammar#name_of_nt nt
  
  method nt_body (nt : nt_id) : hterm = nt_bodies.(nt)

  method hterms_count : int = next_hterms_id

  method hterm_arity (id : hterms_id) : int = List.length @@ self#id2hterms id

  method id2hterms (id : hterms_id) : hterm list =
    let hterms, _, _, _ = hterms_data.(id) in
    hterms

  method id2terms (id : hterms_id) : Grammar.term list =
    let _, terms, _, _ = hterms_data.(id) in
    terms

  method id2vars (id : hterms_id) : vars =
    let _, _, vars, _ = hterms_data.(id) in
    vars

  method id2nt (id : hterms_id) : nt_id option =
    let _, _, _, nt = hterms_data.(id) in
    nt

  (* --- operations --- *)
  
  (** Changes (H, [ID]) into (H, [arg 1, arg 2, ...]) and (H, [ID1, ID2, ...]) into
      (H, [arg 1-1, arg 1-2, ..., arg 2-1, arg 2-2, ...]), i.e., dereferences the ids into
      a list of hterms. *)
  method decompose_hterm (hterm: hterm) : head * hterm list =
    let h, termids = hterm in
    let hterms =
      match termids with
      | [] -> []
      | [id] ->
        self#id2hterms id
      | _ -> 
        List.rev_append
          (List.fold_left
             (fun hterms id ->
                let hterms' = self#id2hterms id in
                List.rev_append hterms' hterms) [] termids) []
    in
    (h, hterms)

  method headvars_in_nt (nt : nt_id) : vars =
    headvars_in_term @@ snd @@ grammar#rule nt

  (** List of all nonterminals in terms without duplicates. *)
  method nt_in_terms (terms : term list) : nts =
    match terms with
    | [] -> SortedNTs.empty
    | t :: terms' -> SortedNTs.merge (nt_in_term t) (self#nt_in_terms terms')

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
  method nt_in_term_with_linearity (term : term) : nts * nts =
    match term with
    | T _ | Var _ -> (SortedNTs.empty, SortedNTs.empty)
    | NT f -> (SortedNTs.singleton f, SortedNTs.empty)
    | App _ ->
      let h, terms = decompose_term term in
      match h with
      | NT f -> let nts = self#nt_in_terms terms in
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

  method nt_in_terms_with_linearity terms i (nts1, nts2) : nts * nts =
    match terms with (* iteration over terms and linearity info simultaneously *)
    | [] -> (nts1, nts2) 
    | t :: terms' ->
      let (nts1', nts2') = self#nt_in_term_with_linearity t (* recursively *) in
      let (nts1'', nts2'') = self#merge_nts_lin (nts1', nts2') (nts1, nts2) in
      self#nt_in_terms_with_linearity terms' (i + 1) (nts1'', nts2'')
  
  method nt_in_nt_with_linearity (nt : nt_id) : nts * nts =
    let term = snd @@ grammar#rule nt in
    self#nt_in_term_with_linearity term

  method nts_in_hterms (nt : nt_id) : nts =
    let terms = self#id2terms nt in (* and is in applicative form list of terms,
                                           and has variables vars *)
    self#nt_in_terms terms

  (* --- construction --- *)

  method private new_hterms_id =
    let x = next_hterms_id in
    next_hterms_id <- x + 1;
    x

  method private term2head h =
    match h with
    | T a -> HT a
    | NT(f) -> HNT(f)
    | Var(x) -> HVar(x)
    | _ -> assert false

  method vars_in_hterm (h, ids : hterm) : vars =
    let vs1 =
      match h with
      | HVar x -> SortedVars.singleton x
      | _ -> SortedVars.empty
    in
    List.fold_left (fun vs id -> SortedVars.merge vs (self#id2vars id)) vs1 ids

  method vars_in_hterms (hterms : hterm list) : vars =
    List.fold_left
      (fun vars hterm ->
         SortedVars.merge vars (self#vars_in_hterm hterm))
      SortedVars.empty hterms

  method private hterm_nt (vars : vars) : nt_id option =
    if SortedVars.is_empty vars then
      None
    else
      Some (fst (SortedVars.hd vars))

  (** Recursively converts a term to hterm. Note that hterms converted this way and present in
      nonterminal bodies never have more than one hterms_id. *)
  method private convert_term (t : term) : hterm =
    let h, terms = Grammar.decompose_term t in
    if terms = [] then
      (self#term2head h, []) (* term2head just replaces Xxx with Hxxx constructor with same arg, but only for var, nt, and t *)
    else
      let hterms = List.map self#convert_term terms in (* recursively in arg terms *)
      let id =
        try
          Hashtbl.find tab_terms_id hterms (* find list of args in tab_terms_id to get its id *)
        with Not_found ->
          begin
            let id = self#new_hterms_id in (* or make a fresh id *)
            Hashtbl.add tab_terms_id hterms id; (* name these args with that id *)
            let vars = self#vars_in_hterms hterms in (* get ascending list of var ids *)
            hterms_data.(id) <- (hterms, terms, vars, self#hterm_nt vars); (* save in hterms_data what list of terms is under that id - converted arg terms, original arg terms, list of vars used inside, without priority *)
            id
          end
      in
      (self#term2head h, [id]) (* return just the head and id of list of args, note that this fun will only return [] or [id] in snd *)

  method find_term (t : term) : hterm =
    let h, terms = Grammar.decompose_term t in
    if terms = [] then
      (self#term2head h, [])
    else
      let hterms = List.map self#find_term terms in
      let id = Hashtbl.find tab_terms_id hterms in
      (self#term2head h, [id])

  (* --- printing --- *)

  method string_of_head = function
    | HNT nt -> grammar#name_of_nt nt
    | HVar v -> grammar#name_of_var v
    | HT a -> string_of_terminal a

  method string_of_hterm (h, ids : hterm) : string =
    self#string_of_head h ^
    String.concat " " (List.map (fun id ->
        let hterms = self#id2hterms id in
        " [" ^
        String.concat " " (List.map (fun t ->
            "(" ^
            self#string_of_hterm t ^
            ")"
          ) hterms) ^
        "]"
      ) ids)

  method string_of_hterms (id : hterms_id) : string =
    Utilities.string_of_list self#string_of_hterm @@ self#id2hterms id

  method print_hterm (hterm : hterm) =
    print_string (self#string_of_hterm hterm)
  
  method print_hterms =
    print_string "hterms_id --> terms\n\n";
    for id = 0 to next_hterms_id - 1 do
      let terms = self#id2terms id in
      if terms <> [] then
        print_string @@ string_of_int id ^ ": " ^
                        String.concat ", " (List.map grammar#string_of_term terms) ^ "\n"
    done

  (* --- debugging --- *)

  (** Locates hterms_id with given path in given hterm. Path consists of integers that mean
      "go to n-th hterms_id list in the list in given hterm" or "go to n-th hterms_id in selected
      list of hterms_ids". The length of the list must be odd. *)
  method locate_hterms_id_in_hterm (h, ids : hterm) (pos : int list) : hterms_id =
    match pos with
    | [] -> failwith "Length of pos must be odd"
    | [i] -> List.nth ids i
    | i :: j :: pos' ->
      let hterms = self#id2hterms (List.nth ids i) in
      let hterm' = List.nth hterms j in
      self#locate_hterms_id_in_hterm hterm' pos'

  (** Locates hterms_id with given path in given nonterminal's body. *)
  method locate_hterms_id (nt : nt_id) (pos : int list) : hterms_id =
    self#locate_hterms_id_in_hterm (self#nt_body nt) pos

  initializer
    (* convert each rule to a normalized form and store in this global array along with its arity (this is ref) *)
    for nt = 0 to grammar#nt_count - 1 do
      let arity, body = grammar#rule nt in
      let hterm = self#convert_term body in
      nt_bodies.(nt) <- hterm (* nt_bodies now contains (arity, (H, [ID])), where H is a var/nonterminal/terminal and ID points in hterms_data at list of terms normalized to (H, [ID]) or (H, []) if there are no args *)
    done;
    if !Flags.debugging then
      begin
        self#print_hterms;
        print_string "\n"
      end
end
