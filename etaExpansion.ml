(** Check the sorts of non-terminals, and print them and the order of the recursion scheme **)
(* Note: the implementation below is naive and slow *)

open Grammar
open GrammarCommon
open Utilities

type tvar = int
(* term sorts *)
type tsort = TSVar of (tsort option) ref | TSFun of tsort * tsort | TSAtom

let dummy_type = TSAtom

let new_tvid () = ref None

let new_tvar () = TSVar (new_tvid ())

let rec deref_st (st : tsort) : tsort =
  match st with
  | TSVar tref ->
    begin
      match !tref with
      | None -> st
      | Some st' ->
        let st1 = deref_st st' in
        tref:= Some st1;
        st1
    end
  | _ -> st

let rec arity2sty (n : int) : tsort =
  if n < 0 then assert false
  else if n = 0 then TSAtom
  else TSFun (TSAtom, arity2sty (n-1))

let rec sty2arity (sty : tsort) : int=
  let sty' = deref_st sty in
  match sty' with
  | TSVar _ -> 0
  | TSAtom -> 0
  | TSFun (_, sty1) -> (sty2arity sty1) + 1

exception UnifFailure of tsort * tsort

let is_stfun sty =
  let sty' = deref_st sty in
  match sty' with
  | TSFun _ -> true
  | _ -> false

let subst_id = []

let rec app_subst sub st =
  match st with
  | TSVar v -> (try List.assoc v sub with Not_found -> st)
  | TSFun(st1,st2) -> TSFun(app_subst sub st1, app_subst sub st2)
  | _ -> st

let rec inst_var (st : tsort) : tsort =
  let st' = deref_st st in
  match st' with
  | TSVar vref -> TSAtom
  | TSFun(st1,st2) -> TSFun(inst_var st1, inst_var st2)
  | _ -> st'

let comp_subst sub1 sub2 =
  let sub1' = List.map (fun (x,st) -> (x, app_subst sub2 st)) sub1 in
  let dom1 = List.map fst sub1 in
  let sub2' = List.filter (fun (x,st) -> not(List.mem x dom1)) sub2 in
  sub1'@sub2'

let rec occur v sty =
  match sty with
  | TSVar(v1) -> v==v1
  | TSFun(sty1,sty2) -> (occur v sty1)||(occur v sty2)
  | _ -> false

(* effectively graph of relations between elements is kinda like find-union but without keeping height of the tree *)
let rec unify_sty sty1 sty2 =
  let sty1' = deref_st sty1 in
  let sty2' = deref_st sty2 in
  match sty1', sty2' with
  | TSVar v1, TSVar v2 ->
    if not (v1 == v2) then
      v1 := Some sty2'
  | TSVar v1, _ ->
    if occur v1 sty2' then
      raise_notrace (UnifFailure (sty1', sty2'))
    else
      v1 := Some sty2'
  | _, TSVar v2 -> 
    if occur v2 sty1' then
      raise_notrace (UnifFailure (sty1', sty2'))
    else
      v2 := Some sty1'
  | TSFun (st11, st12), TSFun (st21, st22) ->
    unify_sty st11 st21;
    unify_sty st12 st22
  | TSAtom, TSAtom -> ()
  | _ -> raise_notrace (UnifFailure (sty1, sty2))

(** Starting with pairs like tvar P ~ fun X Y or any type ~ type, it updates what vars actually point at through unification, i.e., vars' contents will be equal to appropriate type. Some vars may remain if we unify two vars. *)
let rec unify_all c =
  match c with
  | [] -> ()
  | (sty1, sty2) :: c1 ->
    unify_sty sty1 sty2;
    unify_all c1

let rec stys2sty stys =
  match stys with
  | [] -> new_tvar ()
  | [sty] -> sty
  | sty::stys' ->
    let sty1 = stys2sty stys' in
    unify_sty sty sty1;
    sty

let rec string_of_sty (sty : tsort) : string =
  match sty with
  | TSVar tv -> "'a" ^ string_of_int (Obj.magic @@ Obj.repr tv)
  | TSAtom -> "o"
  | TSFun (sty1, sty2) ->
    let left =
      if is_stfun sty1 then
        "(" ^ string_of_sty sty1 ^ ")"
      else
        string_of_sty sty1
    in
    left ^ " -> " ^ string_of_sty sty2

let string_of_nste gram nste : string =
  "Sorts of nonterminals:\n" ^
  String.concat "\n" @@ array_listmap nste (fun i sty ->
      "  " ^ gram#name_of_nt i ^ " : " ^ string_of_sty sty
    )

let lookup_stype_nt f nste = nste.(f)
let lookup_stype_var v vste = vste.(snd v)

(** Produce a type of a term and type variables (unnamed) to unify later.
    fst of result will be the type (e.g., type var for app),
    snd of result will be a list of pairs (fun tvar, STFun(arg tvar, res tvar)).
    All type variables are anonymous, i.e., don't point at anything, however,
    actual pointers are preserved (ocaml objects' addresses), so tvar's physical
    address effectively becomes its id. *)
let rec tcheck_term t vte nte =
  match t with
  | TE A -> (arity2sty 1, [])
  | TE B -> (arity2sty 2, [])
  | TE E -> (arity2sty 0, [])
  | TE T -> (arity2sty 2, [])
  | NT f -> (lookup_stype_nt f nte, [])
  | Var v -> (lookup_stype_var v vte, [])
  | App (t1,t2) ->
    let (sty1, c1) = tcheck_term t1 vte nte in
    let (sty2, c2) = tcheck_term t2 vte nte in
    let sty3 = new_tvar () in
    let sty4 = TSFun (sty2, sty3) in
    (sty3, (sty1, sty4) :: (c2 @ c1))

let rec mk_functy stys sty =
  match stys with
  | [] -> sty
  | sty1 :: stys' ->
    TSFun (sty1, mk_functy stys' sty)

let tcheck_rule f (arity, body) nste =
  let vste : tsort array = Array.make arity dummy_type in
  for i = 0 to arity - 1 do
    vste.(i) <- new_tvar ()
  done;
  (* type var for each rule *)
  let sty, c1 = tcheck_term body vste nste in
  let fty1 = mk_functy (Array.to_list vste) sty (* SAtom*) in
  let fty2 = lookup_stype_nt f nste in
  (*    (sty,SAtom):: *) (* add this if we wish to enforce the right-hand side has ground type *)
  (fty1, fty2) :: c1

let tcheck_rules rules nste =
  let cstr = ref [] in
  for i = 0 to Array.length rules - 1 do 
    cstr := (tcheck_rule i rules.(i) nste) @ !cstr
  done;
  !cstr

let rec order_of_sty (sty : tsort) : int =
  match sty with
  | TSFun (sty1, sty2) -> max ((order_of_sty sty1) + 1) (order_of_sty sty2)
  | _ -> 0

let order_of_nste nste =
  let nste' = index_list (Array.to_list nste) in
  let ordmap = List.map (fun (nt, sty) -> (nt, order_of_sty sty)) nste' in
  let x = list_max (fun (nt1, ord1) (nt2, ord2) -> compare ord1 ord2) ordmap in
  x

let string_of_order gram nt ord : string =
  "Order of recursion scheme: " ^ string_of_int ord ^ "\n" ^
  "Non-terminal of highest order: " ^ gram#name_of_nt nt

let rec mk_vste i vste arity sty =
  if i < arity then
    match sty with
    | SFun (sty1, sty') -> 
      vste.(i) <- sty1;
      mk_vste (i + 1) vste arity sty'
    | _ -> assert false (* arity and sty contradict *)

let update_arity_of_nt gram nste =
  for nt = 0 to gram#nt_count - 1 do
    let sty = nste.(nt) in
    let arity = sty2arity sty in
    let arity', body = gram#rule nt in
    if arity > arity' then (* add dummy argument *)
      let vars = List.map (fun i-> Var (nt, i)) (range arity' arity) in
      let body' = Grammar.mk_app body vars in (* add explicit arguments to rules so that the kind of the term inside is o *)
      gram#replace_rule nt (arity, body')
  done

let rec clean_sort : tsort -> sort = function
  | TSAtom -> SAtom
  | TSFun (s1, s2) -> SFun (clean_sort s1, clean_sort s2)
  | TSVar _ -> failwith "Expected no variables when cleaning sorts"

(** Eta-expand each rule in the grammar so that its body is of sort o. Compute sorts of
    nonterminals through unification and save them in the grammar. The sorts in the input are
    ignored. Returns whether the input is a safe term. *)
let eta_expand (gram : grammar) : unit =
  (* creating a new type var for each nonterminal *)
  let num_of_nts = gram#nt_count in
  let nste : tsort array = Array.make num_of_nts dummy_type in
  for i = 0 to num_of_nts - 1 do
    nste.(i) <- new_tvar ()
  done;
  print_verbose !Flags.verbose_preprocessing @@ lazy (
    string_of_nste gram nste ^ "\n"
  );
  (* creating equations for unification *)
  let c = tcheck_rules gram#rules nste in
  (* computing sorts by unification *)
  begin
    try
      unify_all c 
    with
    | UnifFailure (sty1, sty2) ->
      failwith @@ "HORS grammar has rules that are not well-sorted " ^
                  "- could not unify " ^ (string_of_sty @@ deref_st sty1) ^
                  " with " ^ (string_of_sty @@ deref_st sty2)
  end;
  (* saving nonterminal sorts in nste *)
  for i = 0 to num_of_nts - 1 do
    nste.(i) <- inst_var (nste.(i))
  done;
  let f, ord = order_of_nste nste in
  (* eta-expanding bodies of non-terminals so that their bodies are of sort O *)
  update_arity_of_nt gram nste;
  let cleaned_nt_sorts = Array.map clean_sort nste in
  gram#update_sorts cleaned_nt_sorts;
  print_verbose !Flags.verbose_preprocessing @@ lazy (
    string_of_nste gram nste ^ "\n\n" ^
    string_of_order gram f ord
  )
