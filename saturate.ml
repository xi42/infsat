open Flags
open Grammar
open Profiling
open Stype
open Syntax
open Type
open Utilities

(*
type tstate = ity * Stype.st
type delta = (tstate * tr) list
and tr = TrNT of nameNT | TrT of nameT
       | TrApp of tstate * tstate list

let merge_ty ty1 ty2 =
  merge_and_unify compare_ity ty1 ty2

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

(** nteref[f][q] has all typings of nonterminal f that have codomain q. *)
let nteref = ref [||]

(** convert a transition q->q1...qn(=qs) to a negated type, i.e., produce function types
    [q1] -> T -> ... -> T -> q, T -> [q2] -> T -> ... -> q, ..., T -> ... -> T -> qn -> q *)
(* TODO this implementation is really overcomplicated for what it does *)
let rec tr2ty_sub q qs =
  match qs with
    [] -> (ItyQ(Cfa.state2id q), []) (* leaf (q, c) -> . where c is leaf is changed to (state id, []) *)
  | q1::qs' ->
    let (top,ty) = tr2ty_sub q qs' in (* top is always q or T -> ... -> T -> q *)
    let ty'= List.map (fun ity -> mkItyFun([],ity)) ty in
     if q1="top" then
       (mkItyFun([],top), ty') (* if there is a top arg, it is just ignored *)
     else
      (mkItyFun([],top), (mkItyFun([ItyQ(Cfa.state2id q1)],top))::ty')
and tr2ty q qs =
  let (_,ty) = tr2ty_sub q qs in 
    ty

let arity_of a m =
  List.assoc a m.alpha

(** from t make [] -> ... -> [] -> t with n of [] *)
let rec add_topty n ity =
  if n=0 then ity
  else add_topty (n-1) (mkItyFun([],ity))    

let build_ity q n vs =
  let rec go = function
    | 0 -> ItyQ (Cfa.state2id q)
    | k -> 
        let vs = List.filter (fun (i,_) -> n - k + 1 = i) vs in
        let vs = List.map (fun (_,q) -> ItyQ (Cfa.state2id q)) vs in
        let t1 = go (k-1) in
        mkItyFun (List.sort compare_ity vs,t1) in
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

let rec print_ity ity =
  match ity with
   ItyQ x -> print_string ("~"^(Cfa.id2state x))
 | ItyFun(_,ty,ity) ->
     print_string "(";
     print_ty ty;
     print_string "->";
     print_ity ity;
     print_string ")"
and print_ty ty =
  match ty with
    [] -> print_string "top"
  | [ity] -> print_ity ity
  | ity::ty' ->
      print_ity ity;
      print_string "^";
      print_ty ty'

let print_tys tys =
   Array.iter (fun ty-> print_ty ty; print_string " * ") tys

let print_itylist ty =
  List.iter (fun ity ->
      print_ity ity; print_string "\n") ty

let print_nte() =
  print_string "types for nt:\n===========\n";
  for nt=0 to (Array.length (!nteref))-1 do
    print_string ((Grammar.name_of_nt nt)^":\n");
    for q=0 to (Array.length (!nteref).(nt))-1 do
      print_itylist (!nteref).(nt).(q)
    done
  done


let print_cte() =
  print_string "Constant types:\n=============\n";
  Hashtbl.iter
  (fun a tyarray ->
    print_string (a^":\n");
    Array.iter (fun ty -> List.iter (fun ity->print_ity ity;print_string "\n") ty) tyarray)
  cte

(** Typed pointers to lists of intersections of functional types in the form of
    /\_i (/\_a q_ia -> /\_b q_ib -> ... -> q_i)
    used to type aterms. *)
type tyseq = TySeq of (Grammar.ty * (tyseq ref)) list | TySeqNil
type tyseqref = tyseq ref

(** Different typings of aterms, changed in tyseq_*. *)
let terms_te: (tyseqref array ref) = ref (Array.make 0 (ref TySeqNil))

(** Typings of aterms, assigned in enqueue_var_*. *)
let terms_tyss = ref (Array.make 0 (None))

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
(*  print_string "adding:"; print_tys tys;print_string "\n";*)
  let overwritten = tyseq_rem_subtyping tys tyseqref in
  let _ = tyseq_add_wo_subtyping tys tyseqref in
    overwritten

let merged_vte_updated = ref false

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

let rec tyseq2tyss tyseq len =
  match tyseq with
    TySeqNil -> [Array.make len []]
  | TySeq(tyseqlist) ->
      List.fold_left
       (fun tyss (ty,tyseqref) ->
          let tyss1 = tyseq2tyss (!tyseqref) (len+1) in
	  let _ = List.iter (fun tys -> tys.(len) <- ty) tyss1 in
           List.rev_append tyss1 tyss)
       [] tyseqlist

let lookup_terms_te id =
  match (!terms_tyss).(id) with
    Some(tyss) -> tyss
  | None ->
      let tyss = tyseq2tyss(!((!terms_te).(id))) 0 in
              (!terms_tyss).(id) <- Some(tyss); tyss


let print_terms_te() =
  print_string "Types_of_terms:\n=========\n";
  for id=0 to (Array.length !terms_te)-1 do
   if (!Cfa.termid_isarg).(id) then
    let terms = Cfa.id2terms id in
    List.iter (fun t-> print_term t; print_string ", ") terms;
    print_string "\n";
    let tyss = lookup_terms_te id in
    List.iter (fun tys -> print_tys tys;
      print_string "\n") tyss
  else ()
 done

(** Given equally long lists of types t and r it computes if t.(i) <= r.(i) for all i. *)
let rec subtype_tys tys1 tys2 =
  match (tys1,tys2) with
   ([], []) -> true
 | (ty1::tys1', ty2::tys2') ->
      subtype_ty ty1 ty2
     && subtype_tys tys1' tys2'
 | _ -> assert false
*)
    
(** A two-level LIFO queue, with stack of ids in the first one, and arr[id] in the second
    representing another stack. It differs from normal queue in that it locks the fst of dequeued
    first, giving them priority until they are depleted. *)
let worklist_var_ty : ity TwoLayerQueue.t ref = ref (TwoLayerQueue.mk_queue 0)

(*
let worklist_var_ty_wo_overwrite = ref ([], Array.make 1 [])
*)

(** A LIFO queue, with stack of ids in the first one and arr[id] in the second one being a list
    with data that is returned with it and set to [] after dequeue. *)
let updated_nt_ty : ty BatchQueue.t ref = ref (BatchQueue.mk_queue 0)

let worklist_var = ref (SetQueue.make 1)
(*let worklist_var_overwritten = ref (SetQueue.make 1)*)
let worklist_nt = ref (SetQueue.make 1)
let updated_nts = ref (SetQueue.make 1)

(*
let enqueue_var_ty termid tys =
  (*
  let _ = (!terms_tyss).(termid) <- None in (* invalidate the previous type table for id *)
  *)
  let (ids, a) = !worklist_var_ty in
  let x = a.(termid) in
    a.(termid) <- tys::x;
    if x=[] then worklist_var_ty := (termid::ids, a)
    else ()

(** Enqueue (f,ity) if f is not queued yet. Otherwise, prepend ity to ty in already enqueued
    (f,ty). *)
let enqueue_nt_ty f ity =
  let (nts,a) = !updated_nt_ty in
  let x = a.(f) in
    a.(f) <- ity::x;
    if x=[] then updated_nt_ty := (f::nts, a)
    else ()


exception WorklistVarTyEmpty

let rec dequeue_var_ty_gen worklist =
  let (ids, a) = !worklist in
   match ids with
     [] -> raise WorklistVarTyEmpty 
   | id::ids' ->
       match a.(id) with
          [] -> (worklist := (ids',a);
	         dequeue_var_ty_gen worklist)
	| tys::tyss ->
	    a.(id) <- tyss;
	    (if tyss=[] then worklist := (ids',a));
	    (id, tys)

let rec dequeue_var_ty() =
  dequeue_var_ty_gen worklist_var_ty
*)

(*
let rec dequeue_var_ty_wo_overwrite() =
  dequeue_var_ty_gen worklist_var_ty_wo_overwrite
*)
(*
(** Dequeue (f,ty) for some f : ty, where f is a nonterminal and ty its computed types. *)
let dequeue_nt_ty() = 
  let (nts, a) = !updated_nt_ty in
   match nts with
     [] -> raise WorklistVarTyEmpty
   | f::nts' ->
       let ty = a.(f) in
         (updated_nt_ty := (nts',a); a.(f) <- []; (f,ty))
*)
(*
(** Called to save that aterm with given id was computed to have an intersection type ty. *)
let register_terms_te id ty overwrite_flag =
(*  assert (not(ty=[]));*)
 if !Flags.merge_vte then
   let tyseqref = (!terms_te).(id) in
   (merged_vte_updated := false;
     tyseq_merge_tys ty tyseqref;
     if !merged_vte_updated then
       (Utilities.debug ("type of id "^(string_of_int id)^" has been updated\n");
       let tys = List.hd (tyseq2tyss !tyseqref 0) in
       enqueue_var_ty id tys)
     else ())
 else
  let tyseqref = (!terms_te).(id) in
  if overwrite_flag && !Flags.overwrite then
    if tyseq_mem ty tyseqref then () (* if terms_te[id] already has the computed type *)
    else if tyseq_subsumed ty tyseqref (* if terms_te[id] has has a type not less restrictive than
                                          ty, on each argument, we delegate it *)
    then ((*flag_overwritten := true; *)
          SetQueue.enqueue !worklist_var_overwritten id) (* enqueue for replacing *)
    else  (* we can't compare ty with terms_te[id] *)
     (let overwritten = tyseq_add_with_subtyping ty tyseqref in (* more or less remove subtyped
                                                                   stuff from tyseqref and add ty
                                                                   to it *)
      (*         flag_updated_termid := true; *)
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

(** Returns venvs where each venv in venvs is prepended with exactly one ty from tys in every
    combination. *)
let rec mk_prod_venvs (i,j,tys) venvs acc =
  match tys with 
    [] -> acc
  | ty::tys' ->
      let acc' =
        List.fold_left
        (fun venvs1 venv1 ->
           ((i,j,ty)::venv1)::venvs1 ) acc venvs
      in mk_prod_venvs (i,j,tys') venvs acc'

(* env is a list of elements of the form (i,j,id), 
   which means that variables i to j are bound to ti to tj,
   where id is the identifier of [ti;...;tj] *)
let rec mk_venvs env =
  match env with
    [] -> [[]]
  | [(i,j,id)] -> let tys = lookup_terms_te(id) in 
       List.map (fun ty -> [(i,j,ty)]) tys
  | (i,j,id)::env' ->
     let tys = lookup_terms_te(id) in
     if tys=[] then []
     else 
      let venvs = mk_venvs env' in
      if venvs=[] then []
      else
      (* this may blow up the number of type environments *)
        mk_prod_venvs (i,j,tys) venvs []

let rec mk_venvs_incremental env (id,tys) = 
  match env with
    [] -> [[]]
  | (i,j,id1)::env' ->
     if id1=id then
      let venvs = mk_venvs env' in
        List.map (fun venv-> (i,j,tys)::venv) venvs
     else
       let tyss = lookup_terms_te(id1) in
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

(** There was an application where in some aterm the bindings for variables were as in env.
    This function computes what kind of types each variable in given lists of variables had.
    TODO improve desc *)
let rec mk_venvs_mask env =
  match env with
    [] -> [[]]
  | [(i,j,mask,id)] -> 
       let tys = lookup_terms_te(id) in 
       let tys' = if List.length mask=j+1-i then tys
                  else mask_tys i mask tys []
       in  List.map (fun ty -> [(i,j,ty)]) tys'
  | (i,j,mask,id)::env' ->
     let tys = lookup_terms_te(id) in
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
    size l where each venvs[i] corresponds to one of all possible typings of aterms asX, but where
    asX=id, it is replaced with tys. So, it is a cartesian product making all possible typing
    combinations for aterms but with a forced single typing for asX=id. *)
let rec mk_venvs_mask_incremental env (id,tys) =
  match env with
    [] -> [[]]
  | (i,j,mask,id1)::env' ->
     let tyss = if id=id1 then  [tys] else lookup_terms_te(id1) in (* get the type or replaced
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

let rec merge_vtes vtes =
  match vtes with
    [] -> []
 | vte::vtes' ->
   merge_two_vtes vte (merge_vtes vtes')
(** Merges vtes (variable types) by combining the list of type bindings in order, and combining
    types when a binding for the same variable is present in both lists. The resulting binding
    is ordered ascendingly lexicographically by variable ids. Combining types is also idempodently
    merging list of types (i.e., there are sets of types). *)
and merge_two_vtes vte1 vte2 =
  match (vte1,vte2) with
    ([], _) -> vte2
  | (_,[]) -> vte1
  | ((v1,ty1)::vte1', (v2,ty2)::vte2') ->
     let n = compare v1 v2 in
      if n<0 then (v1,ty1)::(merge_two_vtes vte1' vte2)
      else if n>0 then (v2,ty2)::(merge_two_vtes vte1 vte2')
      else (v1,merge_ty ty1 ty2)::(merge_two_vtes vte1' vte2')

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
  Array.fold_left (@) []  (!nteref).(f)


let ty_of_nt_q f q =
  (!nteref).(f).(q)

let ty_of_nt_qs f qs =
  let tyarray = (!nteref).(f) in
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
    NT(f) -> (ty_of_nt_q f q) (* lookup in nteref *)
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
             let ty = ty_of_head_q2 h venv q in (* lookup in nteref or cte what types with
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
(** Computes the types of terms based on constant typing of terminals (cte), available in nteref
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

(*
module X = struct type t = Grammar.term * Grammar.ity
                  let equal (t1,ity1) (t2,ity2) = t1==t2 && (id_of_ity ity1)=(id_of_ity ity2) 
                  let hash = Hashtbl.hash end
module TabCheckTy = Hashtbl.Make(X)
let tab_checkty = TabCheckTy.create 10000
let reset_ty_hash() = TabCheckTy.clear tab_checkty
*)
let reset_ty_hash() = ()
let rec check_ty_of_term venv term ity =
(*
  try
     TabCheckTy.find tab_checkty (term,ity)
  with
    Not_found ->
*) 
 match term with
    App(_,_) ->
     let (h,terms) = Grammar.decompose_term term in
     let tyss = match_head_types h venv (List.length terms) ity in
     let vte = check_argtypes venv terms tyss in vte
(*        (TabCheckTy.replace tab_checkty (term,ity) vte; vte)
*)
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
                                           computed nonterminal types (nteref) for nonterminals,
                                           and given environment for vars *)
     register_terms_te id ty overwrite_flag)
   venvs

(* update the set of types for each term list [t1;...;tk] *)
(** id represents a sequence of terms (aterms). env represents which variables inside them were
    replaced with which other aterms in a single application of nonterminal in which aterms with
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
  | ty::tys' -> mkItyFun(ty,mk_funty_aux tys' ity)

(* given list of pairs (var_id, ty) for each argument aX, it constructs the type of function
   f a1 .. aK, where K is arity and type of value returned by f is ity.
   ((f, 0), ty1), ..., ((f, K), tyK) ~> ty1 -> ... -> tyK -> ity *)
let rec mk_funty_with_vte vte ity arity = 
  mk_funty_with_vte_aux vte ity 0 arity
and mk_funty_with_vte_aux vte ity i arity =
  if i>=arity then ity
  else
    match vte with
       [] -> mkItyFun([], mk_funty_with_vte_aux vte (ity) (i+1) arity)
     | ((_,j),ty)::vte' ->
          if i=j then mkItyFun(ty, mk_funty_with_vte_aux vte' ity (i+1) arity)
          else mkItyFun([], mk_funty_with_vte_aux vte (ity) (i+1) arity)

exception REFUTED

(* Saves in nteref[nt][q] that nt : ity, ity = t1 -> ... -> tK -> q and enqueues nt and nt : ity
   in updated_nts and updated_nt_ty queues.
   nteref[nt][q] is updated to contain only minimal elements after adding ity, essentially
   working as intersection of types. *)
let register_nte nt ity =
  let tyarray = (!nteref).(nt) in
  let q = codom_of_ity ity in
  let ty = tyarray.(q) in (* ty = nteref[nt][q] *)
   if List.exists (fun ity1 -> subtype ity1 ity) ty then () (* do nothing if subtype of the
                                                               computed type is already in
                                                               nteref *)
   else 
      (Cegen.register_nte_for_cegen nt ity q;
       let _ = Utilities.debug ("updated type of nt "^(name_of_nt nt)^"\n") in 
       SetQueue.enqueue !updated_nts nt; (* enqueue nonterminal in updated_nts if it isn't
                                            already queued *)
       enqueue_nt_ty nt ity; (* enqueue f : ity in updated_nt_ty or just add ity to enqueued types
                                if it is already enqueued *)
       let ty' = List.filter (fun ity1->not(subtype ity ity1)) ty in
       (* ty' are types in nteref that are not supertypes of ity *)
       let ty'' = ity::ty' in
(* no need to sort the type of nt *)
(*       let ty'' = merge_ty ty' [ity] in *)
       (!nteref).(nt).(q) <- ty''; (* add current type and update *)
         if nt=0 && id_of_ity ity=0 then raise REFUTED else ()) (* stop if args were S : q0 *)

(** Compute and update the type of aterm termid for all environments that contain id and that have
    the type of this id updated to tys. *)
let update_incremental_ty_of_id termid (id,tys) overwrite_flag = 
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
      if List.exists (fun ity'->subtype ity' ity) (!nteref).(nt).(q) then ()
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
                 not(List.exists (fun ity' ->subtype ity' ity) (!nteref).(nt).(q))) qs in
*)
     let ty = ty_of_term_with_vte_qs venv term qs' in
     let ty' = List.filter (fun (ity,_)-> List.mem (id_of_ity ity) qs') ty in
     List.iter (fun (ity,vte)-> register_nte nt (mk_funty_with_vte vte ity (Grammar.arity_of_nt nt))) ty'
)
  venvs

let prod_vte vtes1 vtes2 =
  match (vtes1,vtes2) with
     (_,[]) -> []
   | ([],_)-> []
   | (_,[[]]) -> vtes1
   | ([[]], _) -> vtes2
   | _ ->
     List.fold_left
     (fun vtes vte1 ->
        let vtes2' = List.rev_map (fun vte2->merge_two_vtes vte1 vte2) vtes2 in
(*        let vtes2' = List.rev_append vtes2' [] in *)
	   List.rev_append vtes2' vtes)
     [] vtes1

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
let rec tcheck_wo_venv term ity =
  match term with
    Var(x) -> [[(x,[ity])]]
  | T(a) ->
      let q = codom_of_ity ity in
      let ty = (ty_of_t_q a q) in
        if List.exists (fun ity1->subtype ity1 ity) ty then
	    [[]] (* this terminal has matching type, but, since it is a terminal, there are no
                    variables involved *)
	else [] (* this terminal has no matching typing *)
  | NT(f) ->
      let q = codom_of_ity ity in
      let ty = (ty_of_nt_q f q) in
        if List.exists (fun ity1->subtype ity1 ity) ty then
	    [[]]
	else []
  | App(_,_) ->
      let (h,terms)=Grammar.decompose_term term in
      let tyss = match_head_ity h [] (List.length terms) ity in (* all found types of arguments
                                                                   to this head grouped by
                                                                   application (i.e., not
                                                                   flattened) *)
       List.fold_left
       (fun vtes tys ->
         (tcheck_terms_wo_venv terms tys)@vtes) [] tyss (* get typings of variables based on
                                                           known typings of arguments *)
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
  let (_,term)=Grammar.lookup_rule f in (* f's def *)
  let qs = (!Cfa.array_st_of_nt).(f) in (* overapproximation of states under which f is applied *)
    List.iter
     (fun q ->
       let ity=ItyQ(q) in (* type "q" *)
       let vtes = tcheck_wo_venv term ity in (* list of lists of pairs (var id, ty);
                                                inner list represents mappings for different
                                                variables *)
       List.iter (fun vte ->
           register_nte f (* intersect f : t1 -> .. -> tK -> q with nteref[f][q], put the result
                             back, and enqueue f and f : type if intersection changed anything. *)
	  (mk_funty_with_vte vte ity (Grammar.arity_of_nt f))) (* this line changes variable type
                                                                  bindings to type of nonterminal
                                                                  where they are defined *)
       vtes) qs
       
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
*)
let has_noheadvar f =
  (!Cfa.array_headvars).(f)=[] && !Flags.eager
(*
let update_ty_of_nt_incremental_for_nt g f ty =
  if has_noheadvar g then
     update_ty_of_nt_inc_wo_venv g f ty
  else
  let (_,term)=Grammar.lookup_rule g in
  let bindings = Cfa.lookup_bindings_for_nt g in
    List.iter (fun (binding,qsref) ->
       update_ty_of_nt_inc_for_nt_sub
          g term binding !qsref f ty) bindings
*)
    
let worklist_nt_binding : Cfa.binding TwoLayerQueue.t ref = ref (TwoLayerQueue.mk_queue 0)

(*
let init_worklist_nt_binding maxnt =
  worklist_nt_binding := ([], Array.make maxnt []);
  updated_nt_ty := ([], Array.make maxnt [])
  
let enqueue_worklist_nt_binding (f,binding) =
  let (nts, a) = !worklist_nt_binding in
  let x = a.(f) in
  if List.mem binding x then ()
  else
    a.(f) <- binding::x;
    if x=[] then worklist_nt_binding := (f::nts, a)
    else ()
*)
exception WorklistBindingEmpty
(*
let rec dequeue_worklist_nt_binding () =
  let (nts, a) = !worklist_nt_binding in
   match nts with
     [] -> raise WorklistBindingEmpty
   | f::nts' ->
       match a.(f) with
          [] -> (worklist_nt_binding := (nts',a);
	         dequeue_worklist_nt_binding ())
	| binding::l ->
	    a.(f) <- l;
	    (if l=[] then worklist_nt_binding := (nts',a));
	    (f,binding)

let remove_worklist_nt_binding nts =
  let (_, a) = !worklist_nt_binding in
   List.iter (fun f -> a.(f) <- []) nts

let print_worklist_nt_binding () =
  let (nts,a) = !worklist_nt_binding in
  List.iter (fun f->
    if not(a.(f)=[]) then print_string ((string_of_int f)^",")) nts;
  print_string "\n"

let add_worklist_nt_binding f =
  let (nts, a) = !worklist_nt_binding in
    a.(f) <- Cfa.lookup_bindings_for_nt f;
    worklist_nt_binding := (f::nts, a)
    
let rec mk_worklist_nt_binding updated_terms =
(*  print_string "calling mk_worklist\n";*)
  try
     let id = SetQueue.dequeue updated_terms in
     let bindings = Cfa.lookup_dep_termid_nt id in
        List.iter enqueue_worklist_nt_binding bindings;
        mk_worklist_nt_binding updated_terms
  with SetQueue.Empty -> ()

(*
let rec mk_worklist_var updated_nts = 
  match updated_nts with
    [] -> []
  | f::updated_nts' ->
      merge_and_unify compare (Cfa.lookup_dep_nt_termid f) (mk_worklist_var updated_nts')
*)

let report_yes() =
  (print_string "The property is satisfied.\n";
   (if !Flags.certificate then (print_cte();print_nte()));
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
    let (id,tys) = dequeue_var_ty_wo_overwrite() in (* worklist_var_ty_wo_overwrite *)
(*   match dequeue_var_ty_wo_overwrite() with
   Some(id,tys) -> 
*)
    let _ = if !Flags.debugging then
             Utilities.debug ("propagating type of id "^(string_of_int id)^" incrementally wo overwrite\n") in
    let ids = Cfa.lookup_dep_id id in
      List.iter (fun id1 -> update_incremental_ty_of_id id1 (id,tys) false) ids;
      let bindings = Cfa.lookup_dep_termid_nt id in
      List.iter (fun binding -> update_incremental_ty_of_nt binding (id,tys)) bindings;
      saturate_vartypes_wo_overwrite()
  with WorklistVarTyEmpty -> proceed := true
(*
  | None -> proceed := true
*)
  );
  if !proceed 
  then if SetQueue.is_empty !updated_nts then ()
       else saturate_vartypes()
  else
    saturate_vartypes_wo_overwrite()
*)

let init_saturation() =
  (* initialize the set of types for variables and non-terminals to empty *)
  let aterms_count = !Cfa.next_aterms_id in
  let nt_count = Grammar.nt_count() in
  (*
  terms_te := Array.make aterms_count (ref TySeqNil); (* terms_te[aterm_id] = ref TySeqNil *)
  terms_tyss := Array.make aterms_count (Some []); (* terms_tyss[aterm_id] = Some [] *)
  for id=0 to aterms_count-1 do (* for each aterm *)
    if (!Cfa.termid_isarg).(id) then (* that is an argument to a nonterminal *)
      (!terms_te).(id) <- ref (TySeq []) (* initialize it with TySeq [] instead of TySeqNil *)
  done;
  nteref := Array.make maxnt [| |];
  for i=0 to maxnt-1 do
    (!nteref).(i) <- Array.make (!num_of_states) [] (* nteref[nt_id][q_id] = [], like nteallref *)
  done;
  *)
  worklist_nt_binding := TwoLayerQueue.mk_queue nt_count;
  worklist_var_ty := TwoLayerQueue.mk_queue aterms_count;
  worklist_var := SetQueue.make aterms_count;
  let _ = for id=0 to aterms_count-1 do 
      if (!Cfa.termid_isarg).(id) then
        SetQueue.enqueue !worklist_var id (* enqueue all aterms that are arguments to nonterminals
                                             with ones with largest id on top (the ones created
                                             last when following the first nonterminal) *)
    done in
  let _ = (worklist_nt := (* queue for nonterminals initialized to ones with arity 0 or with no
                             variables used as functions (head variables, and only if Flags.eager
                             is false) *)
             (* We can further restrict non-terminals to those that are reachable
                from the initial state;
	        however, if f is unreachable, the state set for f is empty, so
	        it does not do much harm to add f here
             *)
             SetQueue.make_fromlist nt_count
               (List.filter (fun f-> arity_of_nt f=0 || has_noheadvar f)
                  (Utilities.fromto 0 nt_count))) in
  let _ = (updated_nts := SetQueue.make nt_count) in (* queue for nonterminals *)
  (*
  if !Flags.debugging then print_nte() else ();
  if !Flags.debugging then print_terms_te() else ();
*)
  ()

let rec saturation_loop() : bool =
  (*
  let proceed = ref false in
  (
    try (* trying to dequeue an aterm : tys (that we have a sequence of asX : tyX) *)
      (* this generally propagates types forward *)
     let (id,tys) = dequeue_var_ty() in (* dequeue from worklist_var_ty *)
(*   match dequeue_var_ty() with
    Some(id,tys) -> 
*)
    let _ = if !Flags.debugging then Utilities.debug ("propagating type of id "^(string_of_int id)^" incrementally\n") in
     let ids = Cfa.lookup_dep_id id in (* ids of aterms that dequeued aterm was applied to
                                         substituting one or more variables inside (propagating
                                         types forward) *)
     (* update type of id1 in envs where there is id, forced to id : tys *)
      List.iter (fun id1 -> update_incremental_ty_of_id id1 (id,tys) true) ids;
      let bindings = Cfa.lookup_dep_termid_nt id in (* nonterminals and their bindings that were
                                                      applied to the aterm id *)
      List.iter (fun binding -> update_incremental_ty_of_nt binding (id,tys)) bindings
(*  | None -> *)
    with WorklistVarTyEmpty ->
   try (* trying nonterminals from updated_nt_ty *)
     let (f,ty) = dequeue_nt_ty() in (* taking care of all new f : ity at once *)
    let _ = if !Flags.debugging then 
            Utilities.debug ("propagating type of nt "^(name_of_nt f)^" incrementally\n") 
    in
    let nts = Cfa.lookup_dep_nt_nt_lin f in
    List.iter (fun g -> update_ty_of_nt_incremental_for_nt g f ty) nts
   with WorklistVarTyEmpty ->
   try (* trying nonterminals from updated_nts *)
    let f = SetQueue.dequeue !updated_nts in
    let ids = Cfa.lookup_dep_nt_termid f in
     List.iter (SetQueue.enqueue !worklist_var) ids;
     let nts = Cfa.lookup_dep_nt_nt f in
        remove_worklist_nt_binding nts;
        List.iter (SetQueue.enqueue !worklist_nt) nts
   with SetQueue.Empty ->
   try (* trying nonterminals from worklist_nt_binding *)
    let (f,binding,qs)=dequeue_worklist_nt_binding() in
     let _ = Utilities.debug ("processing nt "^(Grammar.name_of_nt f)^"\n") in
     update_ty_of_nt f binding qs;
  with WorklistBindingEmpty ->
  try (* trying to type nonterminals from worklist_nt and enqueue nt and nt : type if type
         restricted nonterminal further than before *)
     let f = SetQueue.dequeue !worklist_nt in
      if has_noheadvar f then
        update_ty_of_nt_wo_venv f
      else
        add_worklist_nt_binding f
  with SetQueue.Empty ->
  try
    let id = SetQueue.dequeue !worklist_var (* we take one of enqueued aterms *)
  in
  let _ = Utilities.debug ("processing terms "^(string_of_int id)^"\n") in
  let envs = Cfa.lookup_dep_id_envs id in (* aterms that were (possibly) put into given variables
                                            in aterms with dequeued id (propagating types
                                            backwards) *)
  (* There was an application where aterm id had put some other aterms (env) in given variables
     in its nonterminal - process it.
     *)
  List.iter (fun env-> update_ty_of_id id env true) envs
  with SetQueue.Empty -> proceed := true
   );
   if !proceed then saturate_vartypes_wo_overwrite() 
   else saturate_vartypes()
*)
  false

let saturate() : unit =
  if !Flags.debugging then
    begin
      print_string "Initializing saturation.\n";
      flush stdout
    end;
  profile "initializing saturation" (fun () -> init_saturation());
  if !Flags.debugging then
    begin
      print_string "Starting saturation loop.\n";
      flush stdout
    end;
  profile "saturation" (fun () -> while saturation_loop() do () done)
