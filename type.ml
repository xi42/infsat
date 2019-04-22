open Utilities

(* --- term type --- *)

(** Unique identifier of a single type *)
type ty_id = int

type productivity = bool

(** Type wrapped in a module. *)
module rec Ty :
sig
  (** Fun is a unique identifier of the type, list of arguments and atom codomain. Atoms are
      simply without arguments. *)
  type t = Fun of ty_id * TyList.t list * productivity
  val id_of_ty : t -> int
  val compare : t -> t -> int
  val equal : t -> t -> bool
end =
struct
  (** A single type, i.e. base productive/nonproductive type or part of an intersection type
      /\_i t_i -> t. *)
  type t = Fun of ty_id * TyList.t list * productivity

  (** Each single type has its own identifier. This returns it. *)
  let id_of_ty (Fun (id, _, _)) = id
  
  let compare ty1 ty2 = Pervasives.compare (id_of_ty ty1) (id_of_ty ty2)

  let equal ty1 ty2 = id_of_ty ty1 = id_of_ty ty2
end

(** Intersection type of a function - /\_j (/\ t_ji -> t_j) *)
and TyList : SortedList.SL with type elt = Ty.t = SortedList.Make(struct
    type t = Ty.t
    let compare = Ty.compare
  end)

(** Exposing constructors outside of Ty module. *)
type ty = Ty.t = Fun of ty_id * TyList.t list * productivity
type ity = TyList.t

let ty_np = Fun (0, [], false)
let ty_pr = Fun (1, [], true)
let ity_np = TyList.singleton ty_np
let ity_pr = TyList.singleton ty_pr
let ity_top = TyList.empty

let next_ty_id : ty_id ref = ref 2
let new_ty_id () =
  let x = !next_ty_id in
  next_ty_id := x + 1;
  x

(** Global map of type ids. *)
let fun_ty_ids : (ty_id list list * productivity, ty) Hashtbl.t =
  let h = Hashtbl.create 1024 in
  (* manually adding np and pr *)
  Hashtbl.add h ([], false) ty_np;
  Hashtbl.add h ([], true) ty_pr;
  h

(** Given arg_ity /\_i t_i and res_ty t_r finds unique identifier of the type /\_i t_i -> t_r and
    return the type with that identifier built in. If such a type was not assigned a unique
    identifier yet, it assigns it. *)
let mk_fun (args : ity list) (productivity : productivity) : ty =
  let arg_ids = List.map (TyList.map Ty.id_of_ty) args in
  try
    Hashtbl.find fun_ty_ids (arg_ids, productivity)
  with
  | Not_found ->
    let id = new_ty_id () in
    let ty = Fun (id, args, productivity) in
    Hashtbl.add fun_ty_ids (arg_ids, productivity) ty;
    ty

let cons_fun (args : ity list) : ty -> ty = function
  | Fun (_, args', p) -> mk_fun (args @ args') p

let rec is_productive : ty -> bool = function
  | Fun (_, _, p) -> p

let with_productivity (p : productivity) : ty -> ty = function
  | Fun (_, args, p') as ty ->
    if p = p' then
      ty
    else
      mk_fun args p

(** Changes t1 -> .. -> tK -> t into ([t1; ..; tK], t). *)
let split_ty (f : ty) (k : int) : ity list * ty =
  match k, f with
  | 0, _ -> ([], f)
  | _, Fun (_, args, productivity) ->
    let args1, args2 = split_list k args in
    (args1, mk_fun args2 productivity)

(** Returns functional type ty with first count arguments removed *)
let remove_args (ty : ty) (count : int) : ty =
  match count, ty with
  | 0, _ -> ty
  | _, Fun (_, args, p) -> mk_fun (from_nth count args) p

(** Alias for singleton intersection types. *)
let sty : ty -> ity = TyList.singleton

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

let string_of_atom : productivity -> string = function
  | false -> "np"
  | true -> "pr"

let rec string_of_ty (ty : ty) : string =
  match ty with
  | Fun (_, [], p) -> string_of_atom p
  | Fun (_, args, p) ->
    String.concat " -> " (List.map string_of_ity args) ^ " -> " ^ string_of_atom p

and string_of_ity (ity : ity) : string =
  let string_of_ty_w_parens ty =
    match ty with
    | Fun (_, [], _) -> string_of_ty ty
    | Fun _ -> "(" ^ string_of_ty ty ^ ")"
  in
  let ity_list = TyList.to_list ity in
  match ity_list with
  | [] -> "T"
  | [ty] -> string_of_ty_w_parens ty
  | ty :: ity' -> string_of_ty_w_parens ty ^ List.fold_left (fun acc ty ->
      " /\\ " ^ string_of_ty_w_parens ty ^ acc
    ) "" ity'

(** The reverse of string_of_ty. Input must be exactly like the one returned by string_of_ty
    except for whitespace or else the behavior is undefined. *)
let rec ty_of_string (ty_str : string) : ty =
  let rec ty_of_string_aux (ty_str : string) (args : ity list) : ty =
    match args, String.trim ty_str with
    | [], "np" -> ty_np
    | [], "pr" -> ty_pr
    | _, "np" -> mk_fun (List.rev args) false
    | _, "pr" -> mk_fun (List.rev args) true
    | _, s ->
      match split_outside_parens s "->" with
      | Some (arg_str, res_str) ->
        ty_of_string_aux res_str (ity_of_string arg_str :: args)
      | None -> failwith "Failed to parse type string"
  in
  ty_of_string_aux ty_str []

and ity_of_string (ity_str : string) : ity =
  match String.trim ity_str with
  | "T" -> TyList.empty
  | "np" -> ity_np
  | "pr" -> ity_pr
  | s ->
    match split_outside_parens s "/\\" with
    | Some (ty_str, ity_str') ->
      TyList.merge
        (TyList.singleton @@ ty_of_string @@ trim_parens @@ String.trim ty_str)
        (ity_of_string @@ String.trim ity_str')
    | None ->
      TyList.singleton @@ ty_of_string @@ trim_parens @@ String.trim s

(* --- hterms type --- *)

(** Typing of each of hterm's arguments. *)
type hty = ity list

(** Lexicographical order on hty. *)
let rec hty_compare : hty -> hty -> int =
  compare_lists TyList.compare

let rec hty_eq (hty1 : hty) (hty2 : hty) : bool = hty_compare hty1 hty2 = 0

let string_of_hty (hty : hty) : string =
  string_of_list string_of_ity hty
