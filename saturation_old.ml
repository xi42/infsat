open Binding
open Grammar
open GrammarCommon
open Profiling
open Sort
open Syntax
open Type
open Typing
open Utilities

(* --- types --- *)

(** Typed pointers to lists of intersections of functional types in the form of
    /\_i (/\_a q_ia -> /\_b q_ib -> ... -> q_i)
    used to type hterms. *)
type tyseq = TySeq of (ity * (tyseq ref)) list | TySeqNil
type tyseqref = tyseq ref

(* --- queues --- *)

(*let prop_hterms_ty_queue_wo_overwrite = ref ([], Array.make 1 [])*)

(*let worklist_var_overwritten = ref (SetQueue.make 1)*)


(* --- logic --- *)

type tstate = ity * st
type delta = (tstate * tr) list
and tr = TrNT of nt_id | TrT of nameT
       | TrApp of tstate * tstate list

let add_ity ity ty =
  if List.exists (fun ity1 -> subtype ity1 ity) ty
  then ty
  else
  merge_ty [ity] (List.filter (fun ity1 -> not(subtype ity ity1)) ty)

let compare_tys tys1 tys2 =
  compare (List.map (List.map id_of_ity) tys1) (List.map (List.map id_of_ity) tys2)

let merge_tyss tyss1 tyss2 =
  merge_and_unify compare_tys tyss1 tyss2
  
let rec eq_ty ty1 ty2 =
  match (ty1,ty2) with
   ([],[]) -> true
 | (ity1::ty1',ity2::ty2') ->
    (id_of_ity ity1 = id_of_ity ity2)
        && eq_ty ty1' ty2'
 | _ -> false
let rec eq_tys tys1 tys2 =
  match (tys1,tys2) with
   ([],[]) -> true
 | (ty1::tys1',ty2::tys2') ->
     eq_ty ty1 ty2 && eq_tys tys1' tys2'
 | _ -> false
let add_tyss tys tyss =
  if List.exists (fun tys1 -> eq_tys tys tys1) tyss then
    tyss
  else tys::tyss

let rec eq_tyarray_mask j mask tys1 tys2 =
  List.for_all (fun i ->eq_ty tys1.(i-j) tys2.(i-j)) mask


let emptyTE = []

(** convert a transition q->q1...qn(=qs) to a negated type, i.e., produce function types
    [q1] -> T -> ... -> T -> q, T -> [q2] -> T -> ... -> q, ..., T -> ... -> T -> qn -> q *)
(* TODO this implementation is really overcomplicated for what it does *)
let rec tr2ty_sub q qs =
  match qs with
    [] -> (ItyQ(Cfa.state2id q), []) (* leaf (q, c) -> . where c is leaf is changed to (state id, []) *)
  | q1::qs' ->
    let (top,ty) = tr2ty_sub q qs' in (* top is always q or T -> ... -> T -> q *)
    let ty'= List.map (fun ity -> mk_fun_ty([],ity)) ty in
     if q1="top" then
       (mk_fun_ty([],top), ty') (* if there is a top arg, it is just ignored *)
     else
      (mk_fun_ty([],top), (mk_fun_ty([ItyQ(Cfa.state2id q1)],top))::ty')
and tr2ty q qs =
  let (_,ty) = tr2ty_sub q qs in 
    ty

let arity_of a m =
  List.assoc a m.alpha

(** from t make [] -> ... -> [] -> t with n of [] *)
let rec add_topty n ity =
  if n=0 then ity
  else add_topty (n-1) (mk_fun_ty([],ity))    

let build_ity q n vs =
  let rec go = function
    | 0 -> ItyQ (Cfa.state2id q)
    | k -> 
        let vs = List.filter (fun (i,_) -> n - k + 1 = i) vs in
        let vs = List.map (fun (_,q) -> ItyQ (Cfa.state2id q)) vs in
        let t1 = go (k-1) in
        mk_fun_ty (List.sort compare_ity vs,t1) in
  go n

(** Sets cte to: terminal letter -> array with empty list of types for each state *)
let init_cte terminals st =
  let n = List.length st in
  List.iter (fun (a,_) ->
    Hashtbl.add cte a (Array.make n [])) terminals


let register_cte_ity a ity =
 let tyarray = lookup_cte a in (* get array of types for each state *)
 let x = codom_of_ity ity in (* for t_1 -> ... -> t_n -> q or just q, get q *)
 let ty = tyarray.(x) in
   tyarray.(x) <- merge_and_unify compare [ity] ty (* putting ity into ascending-ordered cte[c][q] *)

let register_cte_ty (a, ty) =
  List.iter (register_cte_ity a) ty

let ata2cte m =
(*  let open AlternatingAutomaton in *)
  init_cte m.AlternatingAutomaton.alpha m.AlternatingAutomaton.st;
  List.iter (fun (a,i) ->
    let l = List.concat (List.map (fun q ->
      let fml = List.assoc (q,a) m.AlternatingAutomaton.delta in
      let pis = AlternatingAutomaton.prime_implicants fml in
      List.map (build_ity q i) pis) m.AlternatingAutomaton.st) in
    register_cte_ty (a,l)) m.AlternatingAutomaton.alpha

(* cte[terminal][q] is a list of types whose codomain is q.
   for all transitions q1 -> ... -> qn -> q, into cte we put
   q1 -> [] -> ... -> [] -> q, ..., [] -> ... -> [] -> qn -> q.
   Also, we put [] -> ... -> [] -> q there for all q such that (q,terminal) has no transitions.
   This is supposed to be a negated version of the automata. Maybe q1 means "not in q1"?
   Also, all qi are as int now and all types ty -> ity have a unique int identifier *)
let automaton2cte m =
  let delta = m.delta in
  init_cte m.alpha m.st; (* cte = terminal -> empty list for each state in m *)
  let _ = List.iter
      (fun ((q, a), qs) -> (* for each transition in the automata *)
        let ty = tr2ty q qs in (* ty is q1 -> [] -> ... -> q, [] -> q2 -> ... -> q where qi is not "top" and with qi as int *)
          register_cte_ty (a, ty))
     delta
  in
  let qs = m.st in
  let terminals = List.map fst m.alpha in
    List.iter
     (fun a ->
        let qs1 = (* the set of q s.t. delta(q,a) is undefined *)
                  List.filter 
                  (fun q-> not(List.exists (fun ((q',a'),_)->q=q'&&a=a') delta))
                  qs
        in register_cte_ty (a, List.map (fun q->add_topty (arity_of a m) (ItyQ(Cfa.state2id q))) qs1)) (* register in cte functions [] -> ... -> [] -> q for all q in qs *)
     terminals

let merged_vte_updated = ref false

(* ----------------- tyseq start ----------------------- *)

(* --- registers --- *)

(** Different typings of hterms, changed in tyseq_*. *)
let hterms_atys : (tyseqref array ref) = ref (Array.make 0 (ref TySeqNil))

(** Cache for converted hterms_atys, assigned in lookup_hterms_atys and invalidated
    when enqueuing vars. *)
let terms_tyss : ity array list option array ref = ref (Array.make 0 (None))

let rec tys2tyseq_singleton tys =
  match tys with
   [] -> TySeqNil
 | ty::tys' ->
     TySeq([(ty, ref (tys2tyseq_singleton tys'))])

(** Checks if there is tys[i] in tyseqref[i] for each i. *)
let rec tyseq_mem tys tyseqref =
  match tys with
    [] -> true
  | ty::tys' ->
      (match !tyseqref with
         TySeqNil -> assert false (* size of the type sequence does not match *)
       | TySeq(tyseqlist) ->
         try
           (* tyseq works like prefix tree *)
              let tyseqref1 = Utilities.assoc_eq eq_ty ty tyseqlist in
                 tyseq_mem tys' tyseqref1
            with Not_found -> false
      )

(** Generally, given tys and tyseqref it checks if for each intersection type ty in position i in
    tys, ty is a supertype of some type in list of intersection types represented by i-th element
    of tyseqref. *)
let rec tyseq_subsumed tys tyseqref =
  match tys with
    [] -> true
  | ty::tys' ->
      (match !tyseqref with
         TySeqNil -> assert false (* size of the type sequence does not match *)
       | TySeq(tyseqlist) ->
              List.exists (fun (ty1,tyseqref1) ->
                 subtype_ty ty1 ty
                && tyseq_subsumed tys' tyseqref1
              ) tyseqlist
      )

(** Adds types tys to tyseqref while memoizing and returns whether tyseqref was modified. *)
let rec tyseq_add_wo_subtyping tys tyseqref =
  match tys with
    [] -> 
      (match !tyseqref with
          TySeqNil -> false
        | _ -> assert false)
  | ty::tys' ->
      (match !tyseqref with
         TySeqNil -> assert false (* size of the type sequence does not match *)
       | TySeq(tyseqlist) ->
            try
              let tyseqref1 = Utilities.assoc_eq eq_ty ty tyseqlist in
                    tyseq_add_wo_subtyping tys' tyseqref1 
            with Not_found -> 
              (tyseqref := TySeq((ty, ref (tys2tyseq_singleton tys'))::tyseqlist); true)
      )

exception TySeqEmptied

(** Removes from tyseqref types tyseqref[i] such that tyseqref[i] <= tys[i]. In other words,
    removes from tyseqref all types that are comparable and not more restrictive than the type
    from corresponding element of tys. *)
let rec tyseq_rem_subtyping_aux tys tyseqref =
  match tys with
    [] -> raise TySeqEmptied
  | ty::tys' ->
      (match !tyseqref with
          TySeqNil -> assert false
        | TySeq(tyseqlist) ->
            let (tyseqlist_subsumed,tyseqlist_not_subsumed) = 
              List.partition (fun (ty1,_) ->  subtype_ty ty ty1) tyseqlist
            in
            let removed = ref false in
            let updated = ref false in
            let tyseqlist1 =
               List.fold_left 
               (fun tyseqlist1' (ty1,tyseqref1) ->
                  try
                    updated := tyseq_rem_subtyping_aux tys' tyseqref1;
                    (ty1,tyseqref1)::tyseqlist1'
                  with TySeqEmptied ->
                    (removed := true; tyseqlist1')
                )
                [] tyseqlist_subsumed
            in if !removed
               then if tyseqlist1=[] && tyseqlist_not_subsumed=[] then raise TySeqEmptied
                    else (tyseqref := TySeq(List.rev_append tyseqlist1 tyseqlist_not_subsumed); true)
               else !updated
      )

let tyseq_rem_subtyping tys tyseqref =
  try tyseq_rem_subtyping_aux tys tyseqref
  with TySeqEmptied -> (tyseqref := TySeq []; true)

(** Merges types tys to tyseqref position-wise while removing less restrictive types present.
    Returns true if it removed some less restrictive types, or false otherwise. *)
let rec tyseq_add_with_subtyping tys tyseqref =
(*  print_string "adding:"; print_ity tys;print_string "\n";*)
  let overwritten = tyseq_rem_subtyping tys tyseqref in
  let _ = tyseq_add_wo_subtyping tys tyseqref in
    overwritten

let rec tyseq_merge_tys tys tyseqref =
  match tys with
    [] -> 
      (match !tyseqref with
          TySeqNil -> ()
        | _ -> assert false)
  | ty::tys' ->
      (match !tyseqref with
         TySeqNil -> assert false (* size of the type sequence does not match *)
       | TySeq(tyseqlist) ->
            match tyseqlist with
              [] -> 
                  merged_vte_updated := true;
                  tyseqref := TySeq((ty, ref (tys2tyseq_singleton tys'))::tyseqlist)
            | (ty1,tyseqref')::tyseqlist' ->
                assert(tyseqlist'=[]);
                tyseq_merge_tys tys' tyseqref';
                let ty2 = merge_and_unify compare_ity ty ty1 in
                if List.length ty1=List.length ty2 then ()
                else (merged_vte_updated:= true;
                      tyseqref := TySeq([(ty2, tyseqref')]))
      )

let rec tyseq2tyss (tyseq : tyseq) (len : int) : ity array list =
  match tyseq with
  | TySeqNil -> [Array.make len TyList.empty]
  | TySeq(tyseqlist) ->
    List.fold_left
      (fun tyss (ty,tyseqref) ->
         let tyss1 = tyseq2tyss (!tyseqref) (len+1) in
   let _ = List.iter (fun tys -> tys.(len) <- ty) tyss1 in
         List.rev_append tyss1 tyss)
      [] tyseqlist

(* TODO this has to be invalidated when enqueuing a var. *)
let lookup_hterms_atys (id : Cfa.hterms_id) : ity array list =
  match (!terms_tyss).(id) with
  | Some(tyss) -> tyss
  | None ->
    let tyss = tyseq2tyss(!((!hterms_atys).(id))) 0 in
    (!terms_tyss).(id) <- Some(tyss);
    tyss

(* ------------------- end tyseq -------------------- *)

(** Given equally long lists of types t and r it computes if t.(i) <= r.(i) for all i. *)
let rec subtype_tys tys1 tys2 =
  match (tys1,tys2) with
   ([], []) -> true
 | (ty1::tys1', ty2::tys2') ->
      subtype_ty ty1 ty2
     && subtype_tys tys1' tys2'
 | _ -> assert false

(** Called to save that hterm with given id was computed to have an intersection type ty. *)
let register_hterms_atys id ty overwrite_flag =
(*  assert (not(ty=[]));*)
 if !Flags.merge_vte then
   let tyseqref = (!hterms_atys).(id) in
   (merged_vte_updated := false;
     tyseq_merge_tys ty tyseqref;
     if !merged_vte_updated then
       (Utilities.debug ("type of id "^(string_of_int id)^" has been updated\n");
       let tys = List.hd (tyseq2tyss !tyseqref 0) in
       enqueue_var_ty id tys)
     else ())
 else
  let tyseqref = (!hterms_atys).(id) in
  if overwrite_flag && !Flags.overwrite then
    if tyseq_mem ty tyseqref then () (* if hterms_atys[id] already has the computed type *)
    else if tyseq_subsumed ty tyseqref (* if hterms_atys[id] has has a type not less restrictive than
                                          ty, on each argument, we delegate it *)
    then (
          SetQueue.enqueue !worklist_var_overwritten id) (* enqueue for replacing *)
    else  (* we can't compare ty with hterms_atys[id] *)
     (let overwritten = tyseq_add_with_subtyping ty tyseqref in (* more or less remove subtyped
                                                                   stuff from tyseqref and add ty
                                                                   to it *)
(*         let _ = Utilities.debug ("updated type of id "^(string_of_int id)^"\n") in*)
         let ty' = Array.of_list ty in
         enqueue_var_ty id ty'; (* enqueue that we found that id : ty for some increasingly
                                   restrictive ty *)
         if overwritten then
           (* enqueue that one of id typings was less restrictive and it was replaced *)
           ((* flag_overwritten := true ; *) SetQueue.enqueue !worklist_var_overwritten id)
         else ()
       )
  else
  let changed = tyseq_add_wo_subtyping ty tyseqref in
  if changed then 
    (let ty' = Array.of_list ty in
     enqueue_var_ty_wo_overwrite id ty' (*;
                                          flag_updated_termid := true *))
  else ()



let rec mk_venvs_incremental env (id,tys) = 
  match env with
    [] -> [[]]
  | (i,j,id1)::env' ->
     if id1=id then
      let venvs = mk_venvs env' in
        List.map (fun venv-> (i,j,tys)::venv) venvs
     else
       let tyss = lookup_hterms_atys(id1) in
       if tyss=[] then []
       else 
        let venvs = mk_venvs_incremental env' (id,tys) in
        if venvs=[] then []
        else
        (* this may blow up the number of type environments *)
         mk_prod_venvs (i,j,tyss) venvs []


let rec mask_ty i mask tys =
  List.iter (fun j ->
     tys.(j-i) <- []) mask
(*
  match (mask,tys) with
    ([],_) -> tys
  | (j::mask',ty::tys') ->
      if i=j then ty::(mask_ty (i+1) mask' tys')
      else []::(mask_ty (i+1) mask tys')
  | _ -> assert false
*)

let rec mask_tys i mask tys r =
   match tys with
     [] -> r
   | ty::tys' ->
       if List.exists (eq_tyarray_mask i mask ty) r then
           mask_tys i mask tys' r
       else
           mask_tys i mask tys' (ty::r)

(** There was an application where in some hterm the bindings for variables were as in env.
    This function computes what kind of types each variable in given lists of variables had.
    TODO improve desc *)
let rec mk_venvs_mask env =
  match env with
    [] -> [[]]
  | [(i,j,mask,id)] -> 
       let tys = lookup_hterms_atys(id) in 
       let tys' = if List.length mask=j+1-i then tys
                  else mask_tys i mask tys []
       in  List.map (fun ty -> [(i,j,ty)]) tys'
  | (i,j,mask,id)::env' ->
     let tys = lookup_hterms_atys(id) in
     if tys=[] then []
     else 
      let venvs = mk_venvs_mask env' in
      if venvs=[] then []
      else
      (* this may blow up the number of type environments *)
       let tys' = if List.length mask=j+1-i then tys
                  else mask_tys i mask tys []
       in mk_prod_venvs (i,j,tys') venvs []

(** Given a list of bindings env with (i,j,vs,asX) of length l, it makes environments venvs of
    size l where each venvs[i] corresponds to one of all possible typings of hterms asX, but where
    asX=id, it is replaced with tys. So, it is a cartesian product making all possible typing
    combinations for hterms but with a forced single typing for asX=id. *)
let rec mk_venvs_mask_incremental env (id,tys) =
  match env with
    [] -> [[]]
  | (i,j,mask,id1)::env' ->
     let tyss = if id=id1 then  [tys] else lookup_hterms_atys(id1) in (* get the type or replaced
                                                                      for id type tys *)
     if tyss=[] then []
     else 
      let venvs = if id=id1 then mk_venvs_mask env' 
                  else mk_venvs_mask_incremental env' (id,tys) in
      if venvs=[] then []
      else
      (* this may blow up the number of type environments *)
       let tyss' = if j-i+1=List.length mask then tyss
                  else mask_tys i mask tyss []
       in mk_prod_venvs (i,j,tyss') venvs []

let rec range_types ty1 ty2 =
  List.fold_left
  (fun ty ity1 ->
     match ity1 with
       ItyFun(_,ty3,ity)->
         if (* not(List.exists (fun ity0 -> subtype ity0 ity) ty)
         && *)
            List.for_all 
            (fun ity3-> List.exists (fun ity2-> subtype ity2 ity3) ty2)
            ty3
         then add_ity ity ty
         else ty
     | _ -> assert false
  ) [] ty1 
 
exception Untypable

let rec size_of_vte vte =
  match vte with
   [] -> 0
 | (_,ty)::vte' -> List.length ty + size_of_vte vte'


let rec pick_smallest_vte ity_vte_list =
  match ity_vte_list with 
      [] -> raise Untypable
   | (_,vte)::ity_vte_list' -> 
      let n = size_of_vte vte in
        pick_smallest_vte_aux ity_vte_list' n vte
and pick_smallest_vte_aux ity_vte_list n vte =
  match ity_vte_list with 
      [] -> vte
   | (_,vte')::ity_vte_list' -> 
      let n' = size_of_vte vte in
        if n'<n then 
          pick_smallest_vte_aux ity_vte_list' n' vte'
        else 
          pick_smallest_vte_aux ity_vte_list' n vte

let pick_vte ity ity_vte_list =
  try
     snd(List.find (fun (ity',vte)-> subtype ity' ity) ity_vte_list )
  with Not_found -> raise Untypable
(*
  let ity_vte_list' = List.filter (fun (ity',vte)-> subtype ity' ity) ity_vte_list in
    pick_smallest_vte ity_vte_list'
*)

let rec insert_ty_with_vte (ity,vte) ty =
  match ty with
    [] -> [(ity,vte)]
 | (ity1,vte1)::ty' ->
      let c= compare_ity ity ity1 in
      if c<0 then (ity,vte)::ty
      else if c>0 then (ity1,vte1)::(insert_ty_with_vte (ity,vte) ty')
      else if size_of_vte vte < size_of_vte vte1 
           then (ity,vte)::ty'
           else ty

let rec range_types_with_vte ty1 ty2 =
  List.fold_left
  (fun ty (ity1,vte1) ->
    match ity1 with 
       ItyFun(_,ty3,ity)->
        ( try
            let vtes = List.map (fun ity3 -> pick_vte ity3 ty2) ty3 in
            let vte' = merge_vtes (vte1::vtes) in
              insert_ty_with_vte (ity,vte') ty
          with Untypable -> ty)
     | _ -> assert false
  ) [] ty1 

let ty_of_nt f =
  Array.fold_left (@) []  (!nt_ity).(f)


let ty_of_nt_q f q =
  (!nt_ity).(f).(q)

let ty_of_nt_qs f qs =
  let tyarray = (!nt_ity).(f) in
  List.fold_left (fun ty q -> List.rev_append tyarray.(q) ty) [] qs

let ty_of_t_qs a qs = 
  let tyarray = lookup_cte a in
  List.fold_left (fun ty q -> List.rev_append tyarray.(q) ty) [] qs

let proj_tys f i tys = tys.(i)

let rec ty_of_var venv (f,i) =
  match venv with 
    [] -> assert false
  | (j1,j2,tys)::venv' ->
    if j1<=i && i<=j2 then
       proj_tys f (i-j1) tys 
    else ty_of_var venv' (f,i)

let rec ty_of_term venv term =
  match term with
   NT(f) -> ty_of_nt f
 | T(a) -> ty_of_t a
 | Var(v) -> ty_of_var venv v 
 | App(t1,t2) ->
    let ty1 = ty_of_term venv t1 in
    let ty2 = ty_of_term venv t2 in
      range_types ty1 ty2

let rec ty_of_term_with_vte venv term =
  match term with
   NT(f) -> List.map (fun ity -> (ity,[])) (ty_of_nt f)
 | T(a) -> List.map (fun ity -> ity,[]) (ty_of_t a)
 | Var(v) -> let ty = ty_of_var venv v in
              List.map (fun ity->(ity,[(v,[ity])])) ty
 | App(t1,t2) ->
    let ty1 = ty_of_term_with_vte venv t1 in
    let ty2 = ty_of_term_with_vte venv t2 in
      range_types_with_vte ty1 ty2

let rec ty_of_term_with_vte_qs venv term qs =
  match term with
   NT(f) -> let ty = ty_of_nt_qs f qs in
               List.map (fun ity -> (ity,[])) ty
 | T(a) -> let ty=ty_of_t_qs a qs in
               List.map (fun ity -> (ity,[])) ty
 | Var(v) -> let ty = ty_of_var venv v in
            let ty' = List.filter (fun ity->List.mem (codom_of_ity ity) qs) ty in
              List.map (fun ity->(ity,[(v,[ity])])) ty'
 | App(t1,t2) ->
    let ty1 = ty_of_term_with_vte_qs venv t1 qs in
    let ty2 = ty_of_term_with_vte venv t2 in
      range_types_with_vte ty1 ty2

(** Split ity = t1 -> .. -> tK -> t for K=arity into ([t1;..;tK], t). *)
let rec split_ity arity ity =
  if arity=0 then ([],ity)
  else match ity with
    ItyFun(_,ty,ity1)->
      let (tys,ity') = split_ity (arity-1) ity1 in
         (ty::tys, ity')
  | _ -> assert false
let rec get_range ity arity =
  if arity=0 then ity
  else 
    match ity with
      ItyFun(_,_,ity1) -> get_range ity1 (arity-1)
    | _ -> assert false

let rec ty_of_head h venv = 
  match h with
   NT(f) -> (ty_of_nt f)
 | T(a) -> (ty_of_t a)
 | Var(v) -> ty_of_var venv v
 | _ -> assert false


let rec ty_of_head_q h venv q = 
  match h with
   NT(f) -> List.map (fun ity -> (ity,[])) (ty_of_nt_q f q)
 | T(a) -> List.map (fun ity -> ity,[]) (ty_of_t_q a q)
 | Var(v) -> let ty = ty_of_var venv v in
              List.map (fun ity->(ity,[(v,[ity])])) ty
 | _ -> assert false

let rec ty_of_head_q2 h venv q = 
  match h with
    NT(f) -> (ty_of_nt_q f q) (* lookup in nt_ity *)
  | T(a) -> (ty_of_t_q a q) (* lookup in cte *)
  | Var(v) -> ty_of_var venv v (* lookup in venv *)
 | _ -> assert false

(** Get a list of first arity arguments, i.e., if arity is k then from a type
    Q_1 -> ... -> Q_k -> q get [Q_1; ...; Q_k]. *)
let rec get_argtys arity ity =
  if arity=0 then []
  else 
    match ity with
      ItyFun(_,ty,ity1) -> ty::(get_argtys (arity-1) ity1)
    | _ -> assert false

(** For given head h, variable environment venv, amount of arguments to the head equal to arity,
    and codomain of searched types ity, it searches for all typings of h found until now that
    have codomain ity and returns a list of lists of types of these arguments alone, where each
    element of the outer list is per one type (i.e., the types of arguments are not flattened).
    Effectively, if h has typings
    /\_i (/\_j q_i,1,j -> /\_j q_i,k,j -> ... -> q_i),
    then it returns [[[q_i,r,j for all j] for r=1..k] for all i such that q_i = ity] *)
let match_head_ity h venv arity ity =
  match ity with
    ItyQ(q) -> (* when ity is base type *)
      (match h with
          Var(v) ->
            if !num_of_states=1 then
              let ty = (ty_of_var venv v) in
                List.map (fun ity1 -> get_argtys arity ity1) ty
            else
            let ty = List.filter (fun ity1->codom_of_ity ity1=q) (ty_of_var venv v) in
              List.map (fun ity1 -> get_argtys arity ity1) ty
        | _ ->
             let ty = ty_of_head_q2 h venv q in (* lookup in nt_ity or cte what types with
                                                   codomain ity does this head have *)
             List.map (fun ity1 -> get_argtys arity ity1) ty
             (* functional ty as triple nested list, but without codomain ite:
                /\_i (/\_j q_i,j -> /\_k q_i,k -> ... -> ?),
                i.e., this contains all possible types of arguments of given nonterminal/terminal
                one outer list element per type, one middle list element per argument, inner list
                is intersection of types of that argument. *)
       )
  | _ ->
   let q = codom_of_ity ity in
    let ty = List.filter (fun ity1 -> 
              subtype (get_range ity1 arity) ity) (ty_of_head_q2 h venv q) in
       List.map (fun ity -> get_argtys arity ity) ty

let match_head_types h venv arity ity =
  match ity with
    ItyQ(q) -> 
      (match h with
          Var(v) -> 
            let ty = (ty_of_var venv v) in
            let ty' = if !num_of_states=1 then
                         ty
                      else List.filter (fun ity1->codom_of_ity ity1=q) ty 
            in
              List.map (fun ity1 -> (get_argtys arity ity1, [(v,[ity1])])) ty'
        | _ ->
             let ty = ty_of_head_q2 h venv q in
              List.map (fun ity1 -> (get_argtys arity ity1, [])) ty
       )
  | _ ->
    let ty = List.filter (fun (ity1,_) -> 
            subtype (get_range ity1 arity) ity) (ty_of_head_q h venv (codom_of_ity ity)) in
      List.map (fun (ity,vte) -> (get_argtys arity ity, vte)) ty

(** Tries to type multiple terms (actually, arguments to something) as elements of tys_ity_list
    with given variable typings venv. Returns new possible typings that are not less or equal
    strict to ones from tys_ity_list. ty is accumulator, initially [].
    tys_ity_list is actually a ty = /\_i ti1 -> .. -> tiK -> ti encoded as a list of
    ([ti1;..;tiK], ti) for each i. *)
let rec check_args tys_ity_list terms venv ty =
  match tys_ity_list with
    [] -> ty
  | (tys,ity)::tys_ity_list' -> (* for each typing of terms *)
    if check_args_aux tys terms venv then (* terms can be types as tys *)
      (if !Flags.merge_vte then
         let ty' = List.filter (fun ity1->not(eq_ity ity ity1)) ty in
         let tys_ity_list'' =
           List.filter (fun (_,ity1)->not(eq_ity ity ity1)) tys_ity_list'
         in
         check_args tys_ity_list'' terms venv (ity::ty')
       else
         (* ty' and tys_ity_list'' are used to remove duplicate types *)
         let ty' = List.filter (fun ity1->not(subtype ity ity1)) ty in (* new codomain typings *)
         let tys_ity_list'' = (* the same thing but for the full term *)
           List.filter (fun (_,ity1)->not(subtype ity ity1)) tys_ity_list'
         in
         check_args tys_ity_list'' terms venv (ity::ty')
      )
    else
      check_args tys_ity_list' terms venv ty
(** Checks if each term from terms can be typed as each respective intersection type in tys. *)
and check_args_aux tys terms venv =
  match (tys,terms) with
    ([], []) -> true
  | (ty::tys', t::terms') ->
       List.for_all (fun ity-> check_term t ity venv) ty
       && check_args_aux tys' terms' venv
  | _ -> assert false
(** Checks if it is possible to type term as type ity with given variable typings venv. *)
and check_term term ity venv =
  match term with
    App(_,_) -> 
     let (h,terms) = Grammar.decompose_term term in
     let tyss = match_head_ity h venv (List.length terms) ity in
       List.exists (fun tys->check_args_aux tys terms venv) tyss
  | Var(v) -> List.exists (fun ity1 -> subtype ity1 ity) (ty_of_var venv v)
  | T(a) -> let q = codom_of_ity ity in
       List.exists (fun ity1 -> subtype ity1 ity) (ty_of_t_q a q)
  | NT(f) -> let q = codom_of_ity ity in
       List.exists (fun ity1 -> subtype ity1 ity) (ty_of_nt_q f q)

(* alternative implementation of ty_of_term *)
(** Computes types of term with given variable typings venv. *)
let ty_of_term2 venv term =
  let (h,terms) = Grammar.decompose_term term in
  let ty = ty_of_head h venv in (* known typings of head *)
  let arity = List.length terms in
  let tys_ity_list = List.map (split_ity arity) ty in
     check_args tys_ity_list terms venv []
(* returns ty list *)
(** Computes the types of terms based on constant typing of terminals (cte), available in nt_ity
    typing of nonterminals, and variable typings from venv. *)
let ty_of_terms venv terms =
  if !(Flags.ty_of_term) then
   List.map (fun term ->
        List.sort compare_ity (ty_of_term venv term)) terms
  else
   List.map (fun term ->
     match term with
       Var(v) -> ty_of_var venv v
      | T(a) -> List.sort compare_ity (ty_of_t a)
      | NT(f) -> List.sort compare_ity (ty_of_nt f)
      | App(_,_) -> List.sort compare_ity (ty_of_term2 venv term)) terms

let rec check_ty_of_term venv term ity =
  match term with
    App(_,_) ->
     let (h,terms) = Grammar.decompose_term term in
     let tyss = match_head_types h venv (List.length terms) ity in
     let vte = check_argtypes venv terms tyss in vte
  | Var(v) ->
    ( try
       let ity1 = List.find (fun ity1 -> subtype ity1 ity) (ty_of_var venv v) in
          [(v, [ity1])]
     with Not_found -> raise Untypable)
  | T(a) ->
      let q = codom_of_ity ity in
       if List.exists (fun ity1 -> subtype ity1 ity) (ty_of_t_q a q)
       then []
       else raise Untypable
  | NT(f) ->
      let q = codom_of_ity ity in
       if  List.exists (fun ity1 -> subtype ity1 ity) (ty_of_nt_q f q)
       then []
       else raise Untypable

and check_argtypes venv terms tyss =
  match tyss with
    [] -> raise Untypable
  | (tys,vte0)::tyss' ->
     ( try
        merge_two_vtes vte0 (check_argtypes_aux venv terms tys)
       with Untypable -> 
         check_argtypes venv terms tyss')
and check_argtypes_aux venv terms tys =
  match (terms,tys) with
    ([], []) -> []
  | (t::terms',ty::tys') ->
      let vtes = List.map (fun ity -> check_ty_of_term venv t ity) ty in
      let vte = check_argtypes_aux venv terms' tys' in
         merge_vtes (vte::vtes)
  | _ -> assert false 


(* incremental version of check_ty_of_term *)
let rec check_ty_of_term_inc venv term ity f tyf =
     let (h,terms) = Grammar.decompose_term term in
     let arity = List.length terms in
     let tyss = 
         if h=NT(f) then
            let ty1 = List.filter (fun ity1 -> subtype (get_range ity1 arity) ity) tyf in
              if ty1=[] then raise Untypable
              else List.map (fun ity -> (get_argtys arity ity, [])) ty1
         else match_head_types h venv arity ity 
     in
     let vte = check_argtypes_inc venv terms tyss f tyf in vte
and check_argtypes_inc venv terms tyss f tyf =
  match tyss with
    [] -> raise Untypable
  | (tys,vte0)::tyss' ->
     ( try
        merge_two_vtes vte0 (check_argtypes_inc_aux venv terms tys f tyf)
       with Untypable -> 
         check_argtypes_inc venv terms tyss' f tyf)
and check_argtypes_inc_aux venv terms tys f tyf =
  match (terms,tys) with
    ([], []) -> []
  | (t::terms',ty::tys') ->
      let vtes = List.map (fun ity -> check_ty_of_term_inc venv t ity f tyf) ty in
      let vte = check_argtypes_inc_aux venv terms' tys' f tyf in
         merge_vtes (vte::vtes)
  | _ -> assert false 



let update_ty_of_id_aux id venvs overwrite_flag = 
  let terms = Cfa.id2terms id in
   List.iter
   (fun venv -> 
     let ty = ty_of_terms venv terms in (* compute type of terms (iteration) in given environment
                                           based on automata typings (cte) for terminals,
                                           computed nonterminal types (nt_ity) for nonterminals,
                                           and given environment for vars *)
     register_hterms_atys id ty overwrite_flag)
   venvs

(* update the set of types for each term list [t1;...;tk] *)
(** id represents a sequence of terms (hterms). env represents which variables inside them were
    replaced with which other hterms in a single application of nonterminal in which hterms with
    id are present. TODO what this does? *)
let update_ty_of_id id env overwrite_flag =
(*  (if !Flags.debugging then
   (print_string ("updating the type for "^(string_of_int id)^"\n");
    Cfa.print_binding env));
*)
  let venvs = mk_venvs_mask env in
  update_ty_of_id_aux id venvs overwrite_flag (* generally, try to get and register an
                                                 intersection type for each term in sequence id *)

let rec mk_funty venv ity = 
  match venv with
    [] -> ity
  | (i,j,ty)::venv' ->
      (* here, we assume that venv=[(i1,j1);...;(ik,jk)] where 
         i_{x+1} = j_x+1
       *)
      let ity' = mk_funty venv' ity in
        mk_funty_aux ty ity'
and mk_funty_aux tys ity =
  match tys with
    [] -> ity
  | ty::tys' -> mk_fun_ty(ty,mk_funty_aux tys' ity)

(* given list of pairs (var_id, ty) for each argument aX, it constructs the type of function
   f a1 .. aK, where K is arity and type of value returned by f is ity.
   ((f, 0), ty1), ..., ((f, K), tyK) ~> ty1 -> ... -> tyK -> ity *)
let rec mk_funty_with_vte vte ity arity = 
  mk_funty_with_vte_aux vte ity 0 arity
and mk_funty_with_vte_aux vte ity i arity =
  if i>=arity then ity
  else
    match vte with
       [] -> mk_fun_ty([], mk_funty_with_vte_aux vte (ity) (i+1) arity)
     | ((_,j),ty)::vte' ->
          if i=j then mk_fun_ty(ty, mk_funty_with_vte_aux vte' ity (i+1) arity)
          else mk_fun_ty([], mk_funty_with_vte_aux vte (ity) (i+1) arity)

(* Saves in nt_ity[nt][q] that nt : ity, ity = t1 -> ... -> tK -> q and enqueues nt and nt : ity
   in prop_nt_queue and prop_nt_ty_queue queues.
   nt_ity[nt][q] is updated to contain only minimal elements after adding ity, essentially
   working as intersection of types. *)
let register_nte nt ity =
  let tyarray = (!nt_ity).(nt) in
  let q = codom_of_ity ity in
  let ty = tyarray.(q) in (* ty = nt_ity[nt][q] *)
  if List.exists (fun ity1 -> subtype ity1 ity) ty then () (* do nothing if subtype of the
                                                              computed type is already in
                                                              nt_ity *)
  else 
    begin
      let _ = Utilities.debug ("updated type of nt "^(name_of_nt nt)^"\n") in 
      SetQueue.enqueue !prop_nt_queue nt; (* enqueue nonterminal in prop_nt_queue if it isn't
                                           already queued *)
      enqueue_nt_ty nt ity; (* enqueue f : ity in prop_nt_ty_queue or just add ity to enqueued types
                               if it is already enqueued *)
      let ty' = List.filter (fun ity1->not(subtype ity ity1)) ty in
      (* ty' are types in nt_ity that are not supertypes of ity *)
      let ty'' = ity::ty' in
      (* no need to sort the type of nt *)
      (*       let ty'' = merge_ty ty' [ity] in *)
      (!nt_ity).(nt).(q) <- ty''; (* add current type and update *)
      if nt=0 && id_of_ity ity=0 then raise REFUTED else () (* stop if args were S : q0 *)
     end

(** Compute and update the type of hterm termid for all environments that contain id and that have
    the type of this id updated to tys. *)
let pupdate_incremental_ty_of_id termid (id,tys) overwrite_flag = 
  let envs = Cfa.lookup_dep_id_envs termid in
   List.iter (fun env -> 
      if List.exists (fun (_,_,_,id1)->id=id1) env then (* for environments of termid which
                                                           contain id *)
        let venvs = mk_venvs_mask_incremental env (id,tys) in
        update_ty_of_id_aux termid venvs overwrite_flag
      else ()
   ) envs

let update_ty_of_nt_aux nt venvs qs =
  let (_,term)=Grammar.lookup_rule nt in
  List.iter 
  (fun venv ->
if not(!(Flags.compute_alltypes)) then
(*     reset_ty_hash();*)
     List.iter (fun q ->
(*  this check actually often slows down
      let ity = mk_funty venv (ItyQ(q)) in
      if List.exists (fun ity'->subtype ity' ity) (!nt_ity).(nt).(q) then ()
      else
*)
        try
         let vte = check_ty_of_term venv term (ItyQ(q)) in
           register_nte nt (mk_funty_with_vte vte (ItyQ(q)) (Grammar.arity_of_nt nt))
        with Untypable -> ()) qs
else
     let qs' = qs in
(* List.filter
              (fun q ->
                 let ity = mk_funty venv (ItyQ(q)) in
                 not(List.exists (fun ity' ->subtype ity' ity) (!nt_ity).(nt).(q))) qs in
*)
     let ty = ty_of_term_with_vte_qs venv term qs' in
     let ty' = List.filter (fun (ity,_)-> List.mem (id_of_ity ity) qs') ty in
     List.iter (fun (ity,vte)-> register_nte nt (mk_funty_with_vte vte ity (Grammar.arity_of_nt nt))) ty'
)
  venvs

let rec tcheck_w_venv venv term ity =
  match term with
    Var(x) -> [[(x,[ity])]]
  | T(a) ->
      let q = codom_of_ity ity in
      let ty = (ty_of_t_q a q) in
        if List.exists (fun ity1->subtype ity1 ity) ty then
      [[]]
  else []
  | NT(f)->  
      let q = codom_of_ity ity in
      let ty = (ty_of_nt_q f q) in
        if List.exists (fun ity1->subtype ity1 ity) ty then
      [[]]
  else []
  | App(_,_) ->
      let (h,terms)=Grammar.decompose_term term in
      let tyss = match_head_types h venv (List.length terms) ity in
       List.fold_left
       (fun vtes (tys,vte1) ->
         let vtes1=tcheck_terms_w_venv venv terms tys in
         let vtes1'= List.rev_map (fun vte0->merge_two_vtes vte0 vte1) vtes1 in
         List.rev_append vtes1' vtes) [] tyss
and tcheck_terms_w_venv venv terms tys =
  match (terms,tys) with
    ([], []) -> [[]]
  | (t::terms', ty::tys') ->
      let vtes1=tcheck_term_ty_w_venv venv t ty in
      let vtes2=tcheck_terms_w_venv venv terms' tys' in
        prod_vte vtes1 vtes2
  | _ -> assert false
and tcheck_term_ty_w_venv venv t ty =
  match ty with
    [] -> [[]]
  | ity::ty' ->
      let vtes1 = tcheck_w_venv venv t ity in
      let vtes2 = tcheck_term_ty_w_venv venv t ty' in
         prod_vte vtes1 vtes2


let update_ty_of_nt_with_merged_vte nt venvs qs =
  Utilities.debug ("updating the type of nt "^(name_of_nt nt)^"\n");
  let (_,term)=Grammar.lookup_rule nt in
  List.iter 
  (fun venv ->
     List.iter (fun q ->
       let vtes = tcheck_w_venv venv term (ItyQ(q)) in
       List.iter (fun vte-> register_nte nt (mk_funty_with_vte vte (ItyQ(q)) (Grammar.arity_of_nt nt)))
         vtes
       ) qs
)
  venvs


let update_ty_of_nt nt binding qs =
 if !Flags.merge_vte then
  let venvs = mk_venvs binding in update_ty_of_nt_with_merged_vte nt venvs qs
 else
  let venvs = mk_venvs binding in update_ty_of_nt_aux nt venvs qs

let update_incremental_ty_of_nt (f,env,qs) (id,tys) = 
  if List.length (List.filter (fun (_,_,id')->id=id') env) =1
  then
    let venvs = mk_venvs_incremental env (id,tys) in
    if !Flags.merge_vte then
      update_ty_of_nt_with_merged_vte f venvs qs
    else
     update_ty_of_nt_aux f venvs qs
  else
    update_ty_of_nt f env qs


(* given a new type f:ity, update the type of g *)

let update_ty_of_nt_inc_for_nt_sub_venv g term venv qs f ty =
  List.iter (fun q ->
   try 
     let vte = check_ty_of_term_inc venv term (ItyQ(q)) f ty in
          register_nte g (mk_funty_with_vte vte (ItyQ(q)) (Grammar.arity_of_nt g))
   with Untypable -> ()) 
  qs


(** Returns types for variables inside assuming that term has codomain ity. *)
let rec tcheck_wo_venv term (target : ty) : (var_id * ity) list list =
  match term with
  | Var(x) ->
    (* x : NP : s, any s *)
    if is_productive target then
      [] (* variables are only NP *)
    else
      (* both NP and PR versions are possible *)
      [[(x, [target])]; [(x, [with_productivity PR target])]]
  | A ->
    (* a : f -> PR : O -> O, f = PR or NP *)
    begin
      match target with
      | Fun(_, _, PR) -> [[]]
      | _ -> []
    end
  | B ->
    (* b : f -> T -> NP, T -> f -> NP : O -> O -> O, f = PR or NP *)
    begin
      match target with
      | Fun(_, [_], Fun(_, [], NP))
      | Fun(_, [], Fun(_, [_], NP)) -> [[]]
      | _ -> []
    end
  | E ->
    (* e : NP : O *)
    begin
      match target with
      | NP -> [[]]
      | _ -> []
    end
  | NT(n) ->
    let f = codom_of_ty ty in
    let nt_ty = (ty_of_nt_q f (is_productive target)) in
    if List.exists (fun ity1->subtype ity1 ity) ty then
      [[]]
    else []
  | App(_,_) ->
    (* target is PR <=>
       - lhs is PR or some arg is PR or there is duplication but all possibilities have to be
         checked
       lhs arg is PR <=>
       - rhs arg is PR or has PR variable

       first compute lhs, then rhs.

       targeting lhs PR:
       - lhs target=*->PR - need to be able to describe * without usual subtyping
       - lhs target=NP
       targeting lhs PR means brute or optimizing checking for duplications
       targeting rhs PR means brute or optimizing checking for PR variables
    *)
    let (h, terms) = Grammar.decompose_term term in
    let tyss = match_head_ity h [] (List.length terms) ity in (* all found types of arguments
                                                                 to this head grouped by
                                                                 application (i.e., not
                                                                 flattened) *)
    List.fold_left
      (fun vtes tys ->
         (tcheck_terms_wo_venv terms tys)@vtes) [] tyss (* get typings of variables based on
                                                           known typings of arguments *)

(** Given a term without head variables, it returns a list of pairs (target type, variable
    types), where target types are types that can be returned by the term, and variable types
    are possible typings of variables with the given target. *)
let tcheck_wo_venv_wo_target term : (ty * venv list) list =
  List.filter (function
      | (_, []) -> false
      | (_, _) -> true)
    (List.map (fun target -> (target, infer_wo_venv term target false)) [NP; PR])

and tcheck_terms_wo_venv terms tys =
  match (terms,tys) with
    ([], []) -> [[]]
  | (t::terms', ty::tys') ->
      let vtes1=tcheck_term_ty_wo_venv t ty in
      let vtes2=tcheck_terms_wo_venv terms' tys' in
        prod_vte vtes1 vtes2
  | _ -> assert false
and tcheck_term_ty_wo_venv t ty =
  match ty with
    [] -> [[]]
  | ity::ty' ->
      let vtes1 = tcheck_wo_venv t ity in
      let vtes2 = tcheck_term_ty_wo_venv t ty' in
         prod_vte vtes1 vtes2

let rec tcheck_wo_venv_inc term ity g ty_g =
  match term with
    Var(x) -> [[(x,[ity])]]
  | T(a) ->
      let q = codom_of_ity ity in
      let ty = (ty_of_t_q a q) in
        if List.exists (fun ity1->subtype ity1 ity) ty then
      [[]]
  else []
  | NT(f)->  
      let ty = if f=g then ty_g else 
               let q = codom_of_ity ity in ty_of_nt_q f q 
      in
        if List.exists (fun ity1->subtype ity1 ity) ty then
      [[]]
  else []
  | App(_,_) ->
      let (h,terms)=Grammar.decompose_term term in
      let arity = List.length terms in
      let tyss =
        if h=NT(g) then
          let ty = List.filter (fun ity1 -> 
              subtype (get_range ity1 arity) ity) ty_g in
          List.map (fun ity -> get_argtys arity ity) ty
        else match_head_ity h [] arity ity
      in
       List.fold_left
       (fun vtes tys ->
         (tcheck_terms_wo_venv_inc terms tys g ty_g)@vtes) [] tyss
and tcheck_terms_wo_venv_inc terms tys g ty_g =
  match (terms,tys) with
    ([], []) -> [[]]
  | (t::terms', ty::tys') ->
      let vtes1=tcheck_term_ty_wo_venv_inc t ty g ty_g in
      let vtes2=tcheck_terms_wo_venv_inc terms' tys' g ty_g in
        prod_vte vtes1 vtes2
  | _ -> assert false
and tcheck_term_ty_wo_venv_inc t ty g ty_g =
  match ty with
    [] -> [[]]
  | ity::ty' ->
      let vtes1 = tcheck_wo_venv_inc t ity g ty_g in
      let vtes2 = tcheck_term_ty_wo_venv_inc t ty' g ty_g in
         prod_vte vtes1 vtes2

(** Computing the type of a nonterminal with no head vars. For each state q under f was applied,
    a type with codomain q is computed for f. *)
let update_ty_of_nt_wo_venv f =
  let (_, term) = Grammar.lookup_rule f in (* f's def *)
  let vtes = tcheck_wo_venv_wo_target term in (* list of lists of pairs (var id, ty);
                                           inner list represents mappings for different
                                                 variables *)
  List.iter (fun (ty, vte) ->
      register_nte f (* intersect f : t1 -> .. -> tK -> q with nt_ity[f][q], put the result
                             back, and enqueue f and f : type if intersection changed anything. *)
  (mk_funty_with_vte vte ty (Grammar.arity_of_nt f))) (* this line changes variable type
                                                                  bindings to type of nonterminal
                                                                  where they are defined *)
    vtes

let update_ty_of_nt_inc_wo_venv f g ty = 
  let _ = Utilities.debug
          ("updating the type of "^(name_of_nt f)^" incrementally\n") in
  let (_,term)=Grammar.lookup_rule f in
  let qs = (!Cfa.array_st_of_nt).(f) in
  let _ = 
    List.iter
     (fun q ->
       let ity=ItyQ(q) in
       let vtes = tcheck_wo_venv_inc term ity g ty in
       List.iter (fun vte ->
         register_nte f
    (mk_funty_with_vte vte ity (Grammar.arity_of_nt f)))
       vtes) qs
  in Utilities.debug ("done!\n")


let update_ty_of_nt_inc_for_nt_sub g term binding qs f ty =
  let venvs = mk_venvs binding in
    List.iter (fun venv -> 
     update_ty_of_nt_inc_for_nt_sub_venv g term venv qs f ty) venvs

let has_noheadvar (f : nt_id) : bool =
  !Cfa.array_headvars.(f) = SortedVars.empty && !Flags.eager


let update_ty_of_nt_incremental_for_nt g f ty =
  if has_noheadvar g then
     update_ty_of_nt_inc_wo_venv g f ty
  else
  let (_,term)=Grammar.lookup_rule g in
  let bindings = Cfa.lookup_nt_bindings g in
    List.iter (fun (binding,qsref) ->
       update_ty_of_nt_inc_for_nt_sub
          g term binding !qsref f ty) bindings

let remove_nt_binding_queue nts =
  let (_, a) = !nt_binding_queue in
   List.iter (fun f -> a.(f) <- []) nts

let print_nt_binding_queue () =
  let (nts,a) = !nt_binding_queue in
  List.iter (fun f->
    if not(a.(f)=[]) then print_string ((string_of_int f)^",")) nts;
  print_string "\n"

let add_nt_binding_queue f =
  let (nts, a) = !nt_binding_queue in
    a.(f) <- Cfa.lookup_nt_bindings f;
    nt_binding_queue := (f::nts, a)
    
let rec mk_nt_binding_queue updated_terms =
(*  print_string "calling mk_worklist\n";*)
  try
     let id = SetQueue.dequeue updated_terms in
     let bindings = Cfa.lookup_dep_termid_nt id in
        List.iter enqueue_nt_binding_queue bindings;
        mk_nt_binding_queue updated_terms
  with SetQueue.Empty -> ()

(*
let rec mk_hterms_queue prop_nt_queue = 
  match prop_nt_queue with
    [] -> []
  | f::prop_nt_queue' ->
      merge_and_unify compare (Cfa.lookup_dep_nt_termid f) (mk_hterms_queue prop_nt_queue')
*)

let report_yes() =
  (print_string "The property is satisfied.\n";
   (if !Flags.certificate then (print_cte();print_nt_ity()));
   if !Flags.outputfile="" then ()
                  else let fp = open_out !Flags.outputfile in
                     (output_string fp ("SATISFIED\n") ; close_out fp))

and saturate_vartypes_wo_overwrite() : unit =
  let proceed = ref false in
  ( try (* typed id with some type that was less or equally strict, did not save it *)
    let id = SetQueue.dequeue !worklist_var_overwritten in
    let _ = Utilities.debug ("processing terms "^(string_of_int id)^" without overwriting\n") in
    let envs = Cfa.lookup_dep_id_envs id in (* what variables were applied to id, bundled per
                                              application *)
      List.iter (fun env-> update_ty_of_id id env false) envs 
  with SetQueue.Empty ->
  try (* typed id : ty in no overwrite mode and saved it *)
    let (id,tys) = dequeue_var_ty_wo_overwrite() in (* prop_hterms_ty_queue_wo_overwrite *)
    let _ = if !Flags.debugging then
             Utilities.debug ("propagating type of id "^(string_of_int id)^" incrementally wo overwrite\n") in
    let ids = Cfa.lookup_dep_id id in
      List.iter (fun id1 -> update_incremental_ty_of_id id1 (id,tys) false) ids;
      let bindings = Cfa.lookup_dep_termid_nt id in
      List.iter (fun binding -> update_incremental_ty_of_nt binding (id,tys)) bindings;
      saturate_vartypes_wo_overwrite()
  with
  | WorklistVarTyEmpty -> proceed := true
  );
  if !proceed 
  then if SetQueue.is_empty !prop_nt_queue then ()
       else saturate_vartypes()
  else
    saturate_vartypes_wo_overwrite()

let print_queue_sizes() =
  if !Flags.debugging then
    begin
      print_string "Queue sizes:\nprop_hterms_ty_queue ";
      print_int (TwoLayerQueue.size !prop_hterms_ty_queue);
      print_string "\nprop_nt_ty_queue ";
      print_int (BatchQueue.size !prop_nt_ty_queue);
      print_string "\nprop_nt_queue ";
      print_int (SetQueue.size !prop_nt_queue);
      print_string "\nnt_binding_queue ";
      print_int (TwoLayerQueue.size !nt_binding_queue);
      print_string "\nnt_queue ";
      print_int (SetQueue.size !nt_queue);
      print_string "\nhterms_queue ";
      print_int (SetQueue.size !hterms_queue);
      print_string "\n\n"
    end

let rec saturation_loop () : bool =
  let proceed = ref true in
  print_queue_sizes();
  begin
    try (* trying to dequeue an hterm : tys (that we have a sequence of asX : tyX) *)
      (* this generally propagates types forward *)
      let (id,tys) = TwoLayerQueue.dequeue !prop_hterms_ty_queue in (* dequeue from prop_hterms_ty_queue *)
      let _ = if !Flags.debugging then Utilities.debug ("propagating type of id "^(string_of_int id)^" incrementally\n") in
    let ids = Cfa.lookup_dep_id id in (* ids of hterms that dequeued hterm was applied to
                                         substituting one or more variables inside (propagating
                                         types forward) *)
    (* update type of id1 in envs where there is id, forced to id : tys *)
    List.iter (fun id1 -> update_incremental_ty_of_id id1 (id,tys) true) ids;
    let bindings = Cfa.lookup_dep_termid_nt id in (* nonterminals and their bindings that were
                                                     applied to the hterm id *)
    List.iter (fun binding -> update_incremental_ty_of_nt binding (id,tys)) bindings
    with TwoLayerQueue.Empty ->
    try (* trying nonterminals from prop_nt_ty_queue *)
      let (f,ty) = BatchQueue.dequeue !prop_nt_ty_queue in (* taking care of all new f : ity at once *)
      let _ = if !Flags.debugging then 
          Utilities.debug ("propagating type of nt "^(name_of_nt f)^" incrementally\n") 
      in
    let nts = Cfa.lookup_dep_nt_nt_lin f in
    List.iter (fun g -> update_ty_of_nt_incremental_for_nt g f ty) nts
    with BatchQueue.Empty ->
    try (* trying nonterminals from prop_nt_queue *)
      let f = SetQueue.dequeue !prop_nt_queue in
      let ids = Cfa.lookup_dep_nt_termid f in
      List.iter (SetQueue.enqueue !hterms_queue) ids;
      let nts = Cfa.lookup_dep_nt_nt f in
    remove_nt_binding_queue nts;
    List.iter (SetQueue.enqueue !nt_queue) nts
    with SetQueue.Empty ->
    try (* trying nonterminals from nt_binding_queue *)
      let (f,binding) = TwoLayerQueue.dequeue !nt_binding_queue in
      let _ = Utilities.debug ("processing nt "^(Grammar.name_of_nt f)^"\n") in
    update_ty_of_nt f binding qs
    with TwoLayerQueue.Empty ->
    try (* trying to type nonterminals from nt_queue and enqueue nt and nt : type if type
           restricted nonterminal further than before *)
      let f = SetQueue.dequeue !nt_queue in
      if has_noheadvar f then
        begin
          Utilities.debug ("Typing nonterminal "^(Grammar.name_of_nt f)^"\n\n");
          update_ty_of_nt_wo_venv f
        end
      else
        begin
          Utilities.debug ("Enqueuing all bindings of nonterminal "^(Grammar.name_of_nt f)^"\n\n")
          add_nt_binding_queue f
        end
    with SetQueue.Empty ->
    try
      let id = SetQueue.dequeue !hterms_queue (* we take one of enqueued hterms *) in
      let _ = Utilities.debug ("Typing hterms "^(string_of_int id)^"\n\n") in
      let envs = Cfa.lookup_dep_id_envs id in (* hterms that were (possibly) put into given variables
                                                 in hterms with dequeued id (propagating types
                                                 backwards) *)
      (* There was an application where hterm id had put some other hterms (env) in given variables
         in its nonterminal - process it.
      *)
    List.iter (fun env-> update_ty_of_id id env true) envs
    with SetQueue.Empty -> proceed := false
  end;
  !proceed
