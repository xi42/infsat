(** Check the sorts of non-terminals, and print them and the order of the recursion scheme **)
(* Note: the implementation below is naive and slow *)

open Grammar
open GrammarCommon
open Utilities

(** Sort variable. *)
type svar = int

(** Term sorts. TSVar contains its currently known type, i.e., it is a type equation. *)
type tsort = TSVar of (tsort option) ref | TSFun of tsort * tsort | TSAtom

(** Sort with metadata where it came from. *)
type msort = tsort * string

let dummy_type = TSAtom

let new_svar_content () = ref None

(** New sort variable. It is necessary to put new_svar_content in a separate function to get
    different pointers. *)
let new_svar () = TSVar (new_svar_content ())

let rec deref_sort (sort : tsort) : tsort =
  match sort with
  | TSVar tref ->
    begin
      match !tref with
      | None -> sort
      | Some sort' ->
        let dsort = deref_sort sort' in
        tref := Some dsort;
        dsort
    end
  | _ -> sort
  
(** Dereference sort in sort with metadata and up. *)
let deref_msort (sort, meta : msort) : msort =
  (deref_sort sort, meta)

let rec arity2sort (n : int) : tsort =
  if n < 0 then
    assert false
  else if n = 0 then
    TSAtom
  else
    TSFun (TSAtom, arity2sort (n - 1))

let rec sort2arity (sort : tsort) : int =
  let sty' = deref_sort sort in
  match sty' with
  | TSVar _ -> 0
  | TSAtom -> 0
  | TSFun (_, sty1) -> (sort2arity sty1) + 1

let msort2arity (sort, _ : msort) : int =
  sort2arity sort

(*
let rec app_subst sub st =
  match st with
  | TSVar v ->
    begin
      try
        List.assoc v sub
      with
      | Not_found -> st
    end
  | TSFun (st1, st2) -> TSFun (app_subst sub st1, app_subst sub st2)
  | _ -> st
*)

(*
let comp_subst sub1 sub2 =
  let sub1' = List.map (fun (x,st) -> (x, app_subst sub2 st)) sub1 in
  let dom1 = List.map fst sub1 in
  let sub2' = List.filter (fun (x,st) -> not(List.mem x dom1)) sub2 in
  sub1'@sub2'
*)

let rec occur v sty =
  match sty with
  | TSVar v1 -> v == v1
  | TSFun (sty1, sty2) -> (occur v sty1) || (occur v sty2)
  | _ -> false

exception UnifFailure of msort * msort

(* effectively graph of relations between elements is kinda like find-union but without keeping height of the tree *)
let rec unify_sty (msort1 : msort) (msort2 : msort) =
  let sort1', meta1 = deref_msort msort1 in
  let sort2', meta2 = deref_msort msort2 in
  match sort1', sort2' with
  | TSVar v1, TSVar v2 ->
    if not (v1 == v2) then
      v1 := Some sort2'
  | TSVar v1, _ ->
    if occur v1 sort2' then
      raise_notrace (UnifFailure (msort1, msort2))
    else
      v1 := Some sort2'
  | _, TSVar v2 -> 
    if occur v2 sort1' then
      raise_notrace (UnifFailure (msort1, msort2))
    else
      v2 := Some sort1'
  | TSFun (arg_sort1, res_sort1), TSFun (arg_sort2, res_sort2) ->
    unify_sty (arg_sort1, "domain of " ^ meta1) (arg_sort2, "domain of " ^ meta2);
    unify_sty (res_sort1, "codomain of " ^ meta1) (res_sort2, "codomain of " ^ meta2)
  | TSAtom, TSAtom -> ()
  | _ -> raise_notrace (UnifFailure (msort1, msort2))

(** Starting with pairs like svar P ~ fun X Y or any type ~ type, it updates what vars actually point at through unification, i.e., vars' contents will be equal to appropriate type. Some vars may remain if we unify two vars. *)
let rec unify_all c =
  match c with
  | [] -> ()
  | (sty1, sty2) :: c1 ->
    unify_sty sty1 sty2;
    unify_all c1

let rec string_of_sort (sort : tsort) : string =
  match sort with
  | TSVar tv ->
    "'a" ^ string_of_int (Obj.magic @@ Obj.repr tv)
  | TSAtom -> "o"
  | TSFun (arg, res) ->
    let left =
      match deref_sort arg with
      | TSFun _ -> "(" ^ string_of_sort arg ^ ")"
      | _ -> string_of_sort arg
    in
    left ^ " -> " ^ string_of_sort res

let string_of_nt_msorts (gram : grammar) (nt_msorts : msort array) : string =
  "Sorts of nonterminals:\n" ^
  String.concat "\n" @@ array_listmap nt_msorts (fun i (sort, _) ->
      "  " ^ gram#nt_name i ^ " : " ^ string_of_sort sort
    )
    
let lookup_stype_nt f nt_msorts = nt_msorts.(f)
let lookup_stype_var v vste = vste.(snd v)

(** Produce a type of a term and type variables (unnamed) to unify later.
    fst of result will be the type (e.g., type var for app),
    snd of result will be a list of pairs (fun svar, STFun(arg svar, res svar)).
    All type variables are anonymous, i.e., don't point at anything, however,
    actual pointers are preserved (ocaml objects' addresses), so svar's physical
    address effectively becomes its id. *)
let rec tcheck_term gram t vte nte : msort * (msort * msort) list =
  match t with
  | TE A -> ((arity2sort 1, "a"), [])
  | TE B -> ((arity2sort 2, "b"), [])
  | TE E -> ((arity2sort 0, "e"), [])
  | TE T -> ((arity2sort 2, "t"), [])
  | NT f -> (lookup_stype_nt f nte, [])
  | Var v -> (lookup_stype_var v vte, [])
  | App (t1, t2) ->
    let ((sort1, _), c1) = tcheck_term gram t1 vte nte in
    let ((sort2, _), c2) = tcheck_term gram t2 vte nte in
    let sort3 = new_svar () in
    let sort4 = TSFun (sort2, sort3) in
    let msort1 = (sort1, gram#string_of_term t1) in
    let msort4 = (sort4, gram#string_of_term t) in
    ((sort3, gram#string_of_term t), (msort1, msort4) :: (c2 @ c1))

let rec mk_fun_sort arg_sorts res_sort =
  match arg_sorts with
  | [] -> res_sort
  | arg_sort :: arg_sorts' ->
    TSFun (arg_sort, mk_fun_sort arg_sorts' res_sort)

let tcheck_rule (gram : grammar) nt (arity, body) nt_msorts : (msort * msort) list =
  let var_sorts : msort array = Array.make arity (dummy_type, "?") in
  for i = 0 to arity - 1 do
    var_sorts.(i) <- (new_svar (), gram#var_name (nt, i))
  done;
  (* type var for each rule *)
  let (sort, meta), unif_eq = tcheck_term gram body var_sorts nt_msorts in
  let nt_sort1 : tsort = mk_fun_sort (List.map fst @@ Array.to_list var_sorts) sort (* SAtom *) in
  let nt_msort2 : msort = lookup_stype_nt nt nt_msorts in
  (* (sty, SAtom) :: *) (* add this if we wish to enforce the right-hand side has ground type *)
  ((nt_sort1, gram#nt_name nt), nt_msort2) :: unif_eq

let tcheck_rules (gram : grammar) (nt_msorts : msort array) : (msort * msort) list =
  let cstr = ref [] in
  for i = 0 to Array.length gram#rules - 1 do 
    cstr := (tcheck_rule gram i gram#rules.(i) nt_msorts) @ !cstr
  done;
  !cstr

let rec order_of_sort (sort : tsort) : int =
  match sort with
  | TSFun (sty1, sty2) -> max ((order_of_sort sty1) + 1) (order_of_sort sty2)
  | _ -> 0

let order_of_nt_msorts nt_msorts : int * int =
  let nt_msorts' = index_list @@ List.map fst @@ Array.to_list nt_msorts in
  let ordmap = List.map (fun (nt, sty) -> (nt, order_of_sort sty)) nt_msorts' in
  let x = list_max (fun (nt1, ord1) (nt2, ord2) -> compare ord1 ord2) ordmap in
  x

let string_of_order gram nt ord : string =
  "Order of recursion scheme: " ^ string_of_int ord ^ "\n" ^
  "Non-terminal of highest order: " ^ gram#nt_name nt

let rec mk_vste i vste arity sty =
  if i < arity then
    match sty with
    | SFun (sty1, sty') -> 
      vste.(i) <- sty1;
      mk_vste (i + 1) vste arity sty'
    | _ -> assert false (* arity and sty contradict *)

let update_arity_of_nt gram nt_msorts =
  for nt = 0 to gram#nt_count - 1 do
    let sort, _ = nt_msorts.(nt) in
    let arity = sort2arity sort in
    let arity', body = gram#rule nt in
    if arity > arity' then (* add dummy argument *)
      let vars = List.map (fun i-> Var (nt, i)) (range arity' arity) in
      (* add explicit arguments to rules so that the kind of the term inside is o *)
      let body' = mk_app body vars in
      gram#replace_rule nt (arity, body')
  done

(** Replaces any remaining variables with sort o. *)
let rec inst_var (sort : tsort) : tsort =
  let st' = deref_sort sort in
  match st' with
  | TSVar vref -> TSAtom
  | TSFun (st1, st2) -> TSFun (inst_var st1, inst_var st2)
  | _ -> st'

let rec clean_sort : tsort -> sort = function
  | TSAtom -> SAtom
  | TSFun (s1, s2) -> SFun (clean_sort s1, clean_sort s2)
  | TSVar _ -> failwith "Expected no variables when cleaning sorts."

(** Eta-expand each rule in the grammar so that its body is of sort o. Compute sorts of
    nonterminals through unification and save them in the grammar. The sorts in the input are
    ignored. Returns whether the input is a safe term. *)
let eta_expand (gram : grammar) : unit =
  (* creating a new type var for each nonterminal *)
  let num_of_nts = gram#nt_count in
  let nt_msorts : msort array = Array.make num_of_nts (dummy_type, "?") in
  for i = 0 to num_of_nts - 1 do
    nt_msorts.(i) <- (new_svar (), "?")
  done;
  print_verbose !Flags.verbose_preprocessing @@ lazy (
    string_of_nt_msorts gram nt_msorts ^ "\n"
  );
  (* creating equations for unification *)
  let c = tcheck_rules gram nt_msorts in
  (* computing sorts by unification *)
  begin
    try
      unify_all c
    with
    | UnifFailure ((sort1, meta1), (sort2, meta2)) ->
      failwith @@ "HORS grammar has rules that are not well-sorted " ^
                  "- could not unify " ^ (string_of_sort @@ deref_sort sort2) ^ " (sort of " ^
                  meta1 ^ ") with " ^ (string_of_sort @@ deref_sort sort2) ^ " (sort of " ^
                  meta2 ^ ")."
  end;
  (* saving nonterminal sorts in nt_msorts *)
  for i = 0 to num_of_nts - 1 do
    let sort, meta = nt_msorts.(i) in
    nt_msorts.(i) <- (inst_var sort, meta)
  done;
  let nt, ord = order_of_nt_msorts nt_msorts in
  (* eta-expanding bodies of non-terminals so that their bodies are of sort O *)
  update_arity_of_nt gram nt_msorts;
  let cleaned_nt_sorts = Array.map (fun (sort, meta) -> clean_sort sort) nt_msorts in
  gram#update_sorts cleaned_nt_sorts;
  print_verbose !Flags.verbose_preprocessing @@ lazy (
    string_of_nt_msorts gram nt_msorts ^ "\n\n" ^
    string_of_order gram nt ord
  )
