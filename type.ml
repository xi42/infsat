open Flags;;
open Utilities;;
open Syntax;;
open Grammar;;
open Automaton;;
open Stype;;

let ity_id = ref 0
let new_ityid() =
 let x = !ity_id in
   (ity_id := x+1; x)

(* better to prepare a separate table for each sort? *)
(** mapping state ids/fun type ids of args and of fun to its type *) 
let itytab = Hashtbl.create 100000

(* global parameters *)
let num_of_states = ref 0
let set_num_of_states(n) =
  num_of_states := n;
  ity_id := n

(** Each type has its own identifier; this returns it. *)
let id_of_ity ity =
  match ity with
    ItyQ(q) -> q
  | ItyFun(id,_,_) -> id


let compare_ity ity1 ity2 =
  compare (id_of_ity ity1) (id_of_ity ity2)

let eq_ity ity1 ity2 =
  (id_of_ity ity1)=(id_of_ity ity2)

(** Changes /\_i t_i -> t into ItyFun(id,ty,ity) with an id unique per type. Assigns this id
    the first time a new function type is constructed. *)
let mkItyFun(ty,ity) =
(*  assert(List.sort compare_ity ty = ty);*)
  let tyids = List.map id_of_ity ty in
  let id1 = id_of_ity ity in
  try
    Hashtbl.find itytab (tyids,id1) 
  with Not_found ->
   let id = new_ityid() in
   let ity = ItyFun(id,ty,ity) in
     (Hashtbl.add itytab (tyids,id1) ity; ity)

(** For a functional or base type /\_i q_i -> /\_j q_j -> ... -> q, returns q. *)
let rec codom_of_ity ity =
  match ity with
    ItyQ x -> x
  | ItyFun(_,_,ity') -> codom_of_ity ity'

let tab_subtype = Hashtbl.create 100000

(** Computes whether aty1 is a subtype of aty2. If Flags.nosubtype is true then it instead computes
    if aty1 = aty2. If Flags.subtype_hash is true then it memoizes the results in tab_subtype.
    t1 <= t2 - t1 is subtype of t2.
    The rules are as follows:
    - q <= q for any base type (state) q
    - t1 -> t2 <= t3 -> t4 iff t3 <= t1 and t2 <= t4
    - /\_i ti <= /\_j rj if for all j there exists i such that ti <= rj
    The intuition is that these types are restrictions and <= is subset relation in the model of
    values that satisfy these restrictions. Removing or weakening these restrictions makes the set
    of elements in the model satisfying them grow. *)
let rec subtype aty1 aty2 =
 if !Flags.nosubtype then id_of_ity aty1=id_of_ity aty2
 else
  match (aty1,aty2) with
    (ItyQ(q1), ItyQ(q2)) -> q1=q2
  | (ItyFun(id1,ty1,aty11), ItyFun(id2,ty2, aty21)) ->
      if !Flags.subtype_hash then 
        if codom_of_ity aty1 = codom_of_ity aty2 then
         try 
           Hashtbl.find tab_subtype (id1,id2)
         with Not_found -> 
         ( let r = (subtype aty11 aty21) && (subtype_ty ty2 ty1)
(*                  (List.for_all (fun aty12 -> List.exists (fun aty22 -> subtype aty22 aty12) ty2) ty1) *)
          in Hashtbl.add tab_subtype (id1,id2) r; r)
        else false
      else (subtype aty11 aty21) && (subtype_ty ty2 ty1)
(*            (List.for_all (fun aty12 -> List.exists (fun aty22 -> subtype aty22 aty12) ty2) ty1)*)
  | _ -> false
(* set-like subset ty1 <= ty2 modulo further subtyping, e.g., [q1,q2] <= [q1] *)
and subtype_ty ty1 ty2 =
   List.for_all (fun ity2 -> List.exists (fun ity1 -> subtype ity1 ity2) ty1) ty2

let rec print_ity ity =
  match ity with
   ItyQ q -> print_string (Ai.id2state q)
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

let cte: (nameT, ty array) Hashtbl.t = Hashtbl.create 100
let lookup_cte c =
  try Hashtbl.find cte c 
  with Not_found -> assert false

let ty_of_t a = 
  Array.fold_left (@) []  (lookup_cte a)
let ty_of_t_q a q = 
  (lookup_cte a).(q)
