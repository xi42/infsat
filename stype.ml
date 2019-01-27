(** Check the sorts of non-terminals, and print them and the order of the recursion scheme **)
(* Note: the implementation below is naive and slow *)

open Utilities
open Grammar

type tvar = int
type st = STvar of (st option) ref | STbase | STfun of st * st 
let dummy_type = STbase

let new_tvid() = ref None

let new_tvar() = STvar(new_tvid())

let rec deref_st st =
  match st with
    STvar(tref) -> 
      ( match !tref with
         None -> st
       | Some(st') -> let st1 = deref_st st' in (tref:= Some(st1); st1))
  | _ -> st

let rec kind_of_sty st =
  match deref_st st with
    | STvar _ | STbase -> O
    | STfun (t1,t2) -> Kfun (kind_of_sty t1,kind_of_sty t2)

let rec arity2sty n =
  if n<0 then assert false
  else if n=0 then STbase
  else STfun(STbase, arity2sty (n-1))

let rec sty2arity sty =
  let sty' = deref_st sty in
  match sty' with
    STvar _ -> 0
  | STbase -> 0
  | STfun(_,sty1) -> (sty2arity sty1) + 1
exception IllSorted of string
exception UnifFailure of st * st

let is_stfun sty =
  let sty' = deref_st sty in
  match sty' with
    STfun _ -> true
  | _ -> false


let subst_id = []

let rec app_subst sub st =
  match st with
     STvar v -> (try List.assoc v sub with Not_found -> st)
   | STfun(st1,st2) -> STfun(app_subst sub st1, app_subst sub st2)
   | _ -> st

let rec inst_var st =
  let st' = deref_st st in
  match st' with
  | STvar vref -> STbase
  | STfun(st1,st2) -> STfun(inst_var st1, inst_var st2)
  | _ -> st'

let comp_subst sub1 sub2 =
  let sub1' = List.map (fun (x,st) -> (x, app_subst sub2 st)) sub1 in
  let dom1 = List.map fst sub1 in
  let sub2' = List.filter (fun (x,st) -> not(List.mem x dom1)) sub2 in
    sub1'@sub2'

let rec occur v sty =
  match sty with
    STvar(v1) -> v==v1
  | STfun(sty1,sty2) -> (occur v sty1)||(occur v sty2)
  | _ -> false

(* effectively graph of relations between elements is kinda like find-union but without keeping height of the tree *)
let rec unify_sty sty1 sty2 =
  let sty1' = deref_st sty1 in
  let sty2' = deref_st sty2 in
   match (sty1',sty2') with
    (STvar v1, STvar v2) ->
        if v1==v2 then ()
        else v1 := Some(sty2')
  | (STvar v1, _) ->
       if occur v1 sty2'
       then raise (UnifFailure (sty1',sty2'))
       else (v1 := Some(sty2'))
  | (_, STvar v2) -> 
       if occur v2 sty1'
       then raise (UnifFailure (sty1',sty2'))
       else (v2 := Some(sty1'))
  | (STfun(st11,st12), STfun(st21,st22)) ->
      unify_sty st11 st21; unify_sty st12 st22
  | (STbase, STbase) -> ()
  | _ -> raise (UnifFailure (sty1,sty2))

(** Starting with pairs like tvar P ~ fun X Y or any type ~ type, it updates what vars actually point at through unification, i.e., vars' contents will be equal to appropriate type. Some vars may remain if we unify two vars. *)
let rec unify_all c =
  match c with
     [] -> []
  | (sty1,sty2)::c1 ->
      unify_sty sty1 sty2;
      unify_all c1

let rec stys2sty stys =
  match stys with
    [] -> new_tvar()
  | [sty] -> sty
  | sty::stys' ->
      let sty1 = stys2sty stys' in
      let _= unify_sty sty sty1 in
         sty

let rec print_sty sty =
  match sty with
    STvar(tv) -> print_string ("'a")
  | STbase -> print_string "o"
  | STfun(sty1,sty2) ->
       let flag1 = is_stfun sty1 in
         (if flag1 then print_string "(" else ();
          print_sty sty1;
          if flag1 then print_string ")" else ();
          print_string " -> ";
          print_sty sty2)
         
let print_sortbinding (f, sty) =
  (print_string (" "^f^" : ");
   print_sty sty;
   print_string "\n")

let print_nste nste =
  let _ = print_string "Sorts of non-terminals:\n" in
  let _ = print_string "=======================\n" in
  let _ = for i=0 to (Array.length nste - 1) do
      print_sortbinding ((name_of_nt i), nste.(i))
    done
  in
  let _ = print_string "\n" in
  ()

let lookup_stype_nt f nste = nste.(f)
let lookup_stype_var v vste = let (_,i) = v in vste.(i)

(** Produce a type of a term and type variables (unnamed) to unify later.
    fst of result will be the type (e.g., type var for app),
    snd of result will be a list of pairs (fun tvar, STFun(arg tvar, res tvar)).
    All type variables are anonymous, i.e., don't point at anything, however,
    actual pointers are preserved (ocaml objects' addresses), so tvar's physical
    address effectively becomes its id. *)
let rec tcheck_term t vte nte =
  match t with
  | NT(f) -> (lookup_stype_nt f nte, [])
  | A -> (arity2sty 1, [])
  | B -> (arity2sty 2, [])
  | E -> (arity2sty 0, [])
  | Var(v) -> (lookup_stype_var v vte, [])
  | App(t1,t2) ->
       let (sty1, c1) = tcheck_term t1 vte nte in
       let (sty2, c2) = tcheck_term t2 vte nte in
       let sty3 = new_tvar() in
       let sty4 = STfun(sty2, sty3) in
       (sty3, (sty1, sty4) :: (c2 @ c1))

let rec mk_functy stys sty =
  match stys with
    [] -> sty
  | sty1::stys' ->
       STfun(sty1, mk_functy stys' sty)

let tcheck_rule f (arity, body) nste =
  let vste = Array.make arity dummy_type in
  let _ = for i=0 to arity-1 do
      vste.(i) <- new_tvar()
    done
  in (* type var for each rule *)
  let (sty,c1) = tcheck_term body vste nste in
  let fty1 = mk_functy (Array.to_list vste) sty (* STbase*) in
  let fty2 = lookup_stype_nt f nste in
  (*    (sty,STbase):: *) (* add this if we wish to enforce the righthand side has ground type *)
  (fty1,fty2)::c1

let tcheck_rules rules nste =
  let cstr = ref [] in
  for i=0 to Array.length rules - 1 do 
    (cstr := (tcheck_rule i rules.(i) nste)@ !cstr)
  done;
  !cstr

let rec order_of_sty sty =
  match sty with
    STfun(sty1,sty2) -> max ((order_of_sty sty1)+1) (order_of_sty sty2)
  | _ -> 0

let order_of_nste nste =
  let nste' = indexlist (Array.to_list nste) in
  let ordmap = List.map (fun (nt, sty) -> (nt, order_of_sty sty)) nste' in
  let x = list_max (fun (nt1,ord1) ->fun (nt2,ord2) -> compare ord1 ord2) ordmap in
    x

let print_order (f,ord) =
  let _ = print_string ("Order of recursion scheme: "^(string_of_int ord)^"\n") in
  let _ = print_string ("Non-terminal of highest order: "^(name_of_nt f)^"\n") in
    ()

let rec mk_vste i vste arity sty =
  if i>=arity then ()
  else 
    (match sty with
       STfun(sty1,sty') -> 
          vste.(i) <- sty1; mk_vste (i+1) vste arity sty'
     | _ -> assert false (* arity and sty contradict *)
   )

let update_arity_of_nt g nste =
  for f=0 to Array.length g.r - 1 do
    let sty = nste.(f) in
    let arity = sty2arity sty in
    let (arity',body) = g.r.(f) in
    if arity>arity' then (* add dummy argument *)
      let vars = List.map (fun i->Var(f,i)) (fromto arity' arity) in
      let body' = Grammar.mk_app body vars in (* add explicit arguments to rules so that the kind of the term inside is o *)
      g.r.(f) <- (arity,body')
    else ()
  done

let eta_expand() =
  (* creating a new type var for each nonterminal *)
  let g = !Grammar.gram in
  let num_of_nts = Array.length g.nt in
  let nste = Array.make num_of_nts dummy_type in
  let _ = for i=0 to num_of_nts-1 do
      nste.(i) <- new_tvar()
    done 
  in
  let _ = if !Flags.debugging then print_nste nste in
  (* creating equations for unification *)
  let rules = g.r in
  let c = tcheck_rules rules nste in
  (* computing sorts by unification *)
  let _ =  try
      unify_all c 
    with UnifFailure _ ->
      failwith "HORS grammar has rules that are not well-sorted"
  in
  (* saving nonterminal sorts in nste *)
  let _ = for i=0 to num_of_nts-1 do
      nste.(i) <- inst_var (nste.(i))
    done
  in
  let (f,ord) = order_of_nste nste in
  (* eta-expanding bodies of non-terminals so that their bodies are of sort O *)
  update_arity_of_nt g nste;
  if !Flags.debugging then
    begin
      print_nste nste;
      print_order (f, ord)
    end
