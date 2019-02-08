(** Unique identifier of a single type *)
type ty_id = int

module rec
  Ty :
sig
  type t = PR | NP | Fun of ty_id * TyList.t * t
  val compare : t -> t -> int
end =
struct
  (** A single type, i.e. base productive/nonproductive type or part of an intersection type
      /\_i t_i -> t. *)
  type t = PR | NP | Fun of ty_id * TyList.t * t
  let compare ty1 ty2 =
    match ty1, ty2 with
    | Fun (id1, _, _), Fun (id2, _, _) -> Pervasives.compare id1 id2
    | _, Fun _ -> -1
    | Fun _, _ -> 1
    | PR, PR -> 0
    | PR, NP -> -1
    | NP, PR -> 1
    | NP, NP -> 0
end

and

  (** Intersection type of a function - /\_j (/\ t_ji -> t_j) *)
  TyList : SortedList.SL with type elt = Ty.t = SortedList.Make(struct
    type t = Ty.t
    let compare = Ty.compare
  end)

type ty = Ty.t = PR | NP | Fun of ty_id * TyList.t * Ty.t
type ity = TyList.t

let next_ty_id : ty_id ref = ref 2
let new_ty_id() =
  let x = !next_ty_id in
  next_ty_id := x + 1;
  x

(* better to prepare a separate table for each sort? *)
(** mapping state ids/fun type ids of args and of fun to its type *)
let fun_ty_ids : (ty_id list * ty_id, ty) Hashtbl.t = Hashtbl.create 100000

(** Each single type has its own identifier. This returns it. *)
let id_of_ty ty =
  match ty with
  | PR -> 0
  | NP -> 1
  | Fun (id, _, _) -> id

let eq_ty ty1 ty2 =
  (id_of_ty ty1) = (id_of_ty ty2)

(** Given arg_ity /\_i t_i and res_ty t_r finds unique identifier of the type /\_i t_i -> t_r and
    return the type with that identifier built in. If such a type was not assigned a unique
    identifier yet, it assigns it. *)
let mk_fun_ty (arg_ity : ity) (res_ty : ty) : ty =
  let arg_ids = TyList.map id_of_ty arg_ity in
  let res_id = id_of_ty res_ty in
  try
    Hashtbl.find fun_ty_ids (arg_ids, res_id)
  with Not_found ->
   let id = new_ty_id() in
   let ty = Fun(id, arg_ity, res_ty) in
   Hashtbl.add fun_ty_ids (arg_ids, res_id) ty;
   ty

(** Given a single type /\_i t_1i -> ... -> /\_i t_ki -> t, it returns t. *)
let rec codom_of_ty (ty : ty) : ty =
  match ty with
  | Fun (_, _, ty) -> codom_of_ty ty
  | _ -> ty

let rec is_productive (ty : ty) : bool =
  match codom_of_ty ty with
  | PR -> true
  | NP -> false
  | _ -> failwith "Expected PR or NP"

let rec with_productivity (orig : ty) (f : ty) : ty =
  match orig with
  | PR | NP -> f
  | Fun (_, ity, ty) -> mk_fun_ty ity (with_productivity ty f)

let rec flip_productivity (orig : ty) : ty =
  match orig with
  | PR -> NP
  | NP -> PR
  | Fun (_, ity, ty) -> mk_fun_ty ity (flip_productivity ty)

(** Changes t1 -> .. -> tK -> t into ([t1; ..; tK], t). If a non-negative limit is supplied, it
    only splits up to K=limit, otherwise uses maximum K. *)
let ty2list (f : ty) (limit : int) : ity list * ty =
  let rec ty2list_aux (f : ty) (acc : ity list) (count : int) : ity list * ty =
    match f, count with
    | _, 0 -> (List.rev acc, f)
    | Fun (_, ity, ty), _ ->
      ty2list_aux ty (ity :: acc) (count - 1)
    | _, _ ->
      if count < 0 then
        (List.rev acc, f)
      else
        failwith "Limit greater than arity"
  in
  ty2list_aux f [] limit
        
let rec ty2array (f : ty) : ity array * ty =
  let args, res = ty2list f (-1) in
  (Array.of_list args, res)

(** Returns functional type ty with first count arguments removed *)
let rec remove_args (ty : ty) (count : int) : ty =
  match count with
  | 0 -> ty
  | _ -> match ty with
    | Fun (_, _, ty) -> remove_args ty (count - 1)
    | _ -> failwith "Tried to remove more arguments than the function has"

(* TODO design subtyping where NP args may be added/removed
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
*)

(*
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
  Array.fold_left (@) [] (lookup_cte a)

let ty_of_t_q a q = 
  (lookup_cte a).(q)
*)
