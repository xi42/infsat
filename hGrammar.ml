open Grammar
open GrammarCommon

(** All sequences of terms converted into head form and having the same environment
    TODO describe what environment
    have a unique identifier assigned to them. *)
type hterms_id = int
(** Head of a term in head form. *)
type head = HT of terminal | HNT of nt_id | HVar of var_id
(** Hterm is a term in head form. It consists of a head and identifiers of sequences of hterms
    that are its arguments. If hterm is (h, [a1;..;aK]) and aX represents a sequence of terms
    [tX1;..;tXl] for some l then the whole hterm represents an application
    h t11 .. t1A t21 .. t2B .. tK1 .. tKZ. *)
type hterm = head * hterms_id list
(** Node that is enqueued when performing 0CFA analysis. *)

class hgrammar (grammar : grammar) = object(self)
  (** Mapping from int ids to lists of terms. when tab_id_terms[i] = (hterms, terms, vars), then
      hterms is a list of terms [a1; a2; ..; aN], each in head form (h, [i1; i2; ..; iM]).
      h is a terminal, nonterminal, or a variable. iX points at tab_id_terms[iX]. This represents
      an applicative term
      h a11 a12 ... a1K a21 ... aM1 ... aMR
      terms are hterms in the original tree representation, and vars is a list of all free variables
      in terms. Variables are represented as integer tuples (X, Y) for Y-th argument (0-indexed)
      of X-th nonterminal (0-indexed).
      Note that two terms with variables that are used in two different nonterminal definitions will
      have different ids, because variables are tuples (nt_id, var_id) that are disjoint for
      different nonterminal bodies. *)
  val mutable hterms_data : (hterm list * Grammar.term list * SortedVars.t * nt_id option) array = [||]

  (** Reverse of fst hterms_data, i.e., hterms_data[tab_terms_id[hterms]] = (hterms, _, _). *)
  val mutable tab_terms_id = Hashtbl.create 100000
  
  (** After the nonterminals are numbered, this is a map from nonterminals' ids to their bodies in
      head form. Bodies in head form are tuples (h, [as1; as2; ..]), where asX are integers that
      are mapped to lists of terms in head form, i.e., as1 = [a11; a12; ...]. The original tuple
      then represents
      h a11 a12 ... a1n a21 a22 ... a2m ...
      Mappings from asX to lists are in hterms_data. *)
  val mutable normalized_body : hterm array = [||]

  (** Increasing counter for fresh identifiers for hterms (all terms and subterms in head form). *)
  val mutable next_hterms_id : int = 0

  (* --- access --- *)

  method nt_count : int = Array.length normalized_body

  method nt_arity (nt : nt_id) : int = grammar#arity_of_nt nt

  method nt_name (nt : nt_id) : string = grammar#name_of_nt nt
  
  method nt_body (nt : nt_id) = normalized_body.(nt)

  method hterms_count : int = next_hterms_id

  method hterm_arity (id : hterms_id) : int = List.length (self#id2hterms id)

  method id2hterms (id : hterms_id) : hterm list =
    let hterms, _, _, _ = hterms_data.(id) in
    hterms

  method id2terms (id : hterms_id) : Grammar.term list =
    let _, terms, _, _ = hterms_data.(id) in
    terms

  method id2vars (id : hterms_id) : SortedVars.t =
    let _, _, vars, _ = hterms_data.(id) in
    vars

  method id2nt (id : hterms_id) : nt_id option =
    let _, _, _, nt = hterms_data.(id) in
    nt

  (* --- operations --- *)
  
  (** Changes (H, [ID]) into (H, [arg 1, arg 2, ...]) and (H, [ID1, ID2, ...]) into (H, [arg 1-1, arg 1-2, ..., arg 2-1, arg 2-2, ...]), i.e., looks up one layer and combines applications *)
  method decompose_hterm (hterm: hterm) : head * hterm list =
    let (h, termids) = hterm in
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

  method vars_in_hterm (h, ids : hterm) : SortedVars.t =
    let vs1 =
      match h with
      | HVar x -> SortedVars.singleton x
      | _ -> SortedVars.empty
    in
    List.fold_left (fun vs id -> SortedVars.merge vs (self#id2vars id)) vs1 ids

  method vars_in_hterms (hterms : hterm list) : SortedVars.t =
    List.fold_left
      (fun vars hterm ->
         SortedVars.merge vars (self#vars_in_hterm hterm))
      SortedVars.empty hterms

  method private hterm_nt (vars : SortedVars.t) : nt_id option =
    if SortedVars.is_empty vars then
      None
    else
      Some (fst (SortedVars.hd vars))

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

  (* --- printing --- *)

  method print_head = function
    | HNT nt -> print_string (grammar#name_of_nt nt)
    | HVar v -> print_string (grammar#name_of_var v)
    | HT a -> print_string (string_of_terminal a)

  method print_hterm (h, ids : hterm) =
    self#print_head h;
    List.iter (fun id ->
        print_string "[";
        let hterms = self#id2hterms id in
        List.iter (fun t ->
            print_string "(";
            self#print_hterm t;
            print_string ") "
          ) hterms;
        print_string "]";
      ) ids
  
  method print_hterms =
    print_string "hterms_id --> terms\n\n";
    for id = 0 to next_hterms_id - 1 do
      let terms = self#id2terms id in
      if terms <> [] then
        begin
          print_int id;
          print_string ": ";
          print_string (String.concat ", " (List.map grammar#string_of_term terms));
          print_string "\n"
        end
    done

  initializer
    let size = grammar#size in
    hterms_data <- Array.make size ([], [], SortedVars.empty, None); (* for each a-term, i.e., @ x t, where x is not an application *)
    let dummy_hterm : hterm = (HNT (-1), []) in
    normalized_body <- Array.make grammar#nt_count dummy_hterm; (* convert each rule to a normalized form and store in this global array along with its arity (this is ref) *)
    for nt = 0 to grammar#nt_count - 1 do
      let arity, body = grammar#rule nt in
      let hterm = self#convert_term body in
      normalized_body.(nt) <- hterm (* normalized_body now contains (arity, (H, [ID])), where H is a var/nonterminal/terminal and ID points in hterms_data at list of terms normalized to (H, [ID]) or (H, []) if there are no args *)
    done;
    if !Flags.debugging then
      begin
        self#print_hterms;
        print_string "\n"
      end
end
