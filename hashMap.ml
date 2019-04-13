open Utilities

module type HashMapMeta = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
end

module Make (KeyMeta : HashMapMeta) (ValueMeta : HashMapMeta) =
struct
  module H = Hashtbl.Make (KeyMeta)
  open H

  let add = add
  let replace = replace
  let find = find
  let find_opt = find_opt
  
  type t = ValueMeta.t H.t

  let fold_short_circuit (m : t) (acc : 'b) (bottom : 'b)
      (f : KeyMeta.t -> ValueMeta.t -> 'b -> 'b) : 'b =
    try
      H.fold (fun k v acc ->
          if acc = bottom then
            raise_notrace Short_circuit
          else
            f k v acc
        ) m acc
    with
    | Short_circuit ->
      bottom

  let empty () : t = H.create 256

  let is_empty (m : t) : bool = length m = 0

  let singleton (k : KeyMeta.t) (v : ValueMeta.t) : t =
    let m = empty () in
    add m k v;
    m
  
  let merged (v_merge : ValueMeta.t -> ValueMeta.t -> ValueMeta.t) (m1 : t) (m2 : t) : t =
    let m = H.copy m2 in
    m1 |> H.iter (fun nt_ty v ->
        match H.find_opt m nt_ty with
        | Some v' -> H.add m nt_ty (v_merge v' v)
        | None -> H.add m nt_ty v
      );
    m

  let hash (m : t) : int =
    H.fold (fun k v acc ->
        let kh = KeyMeta.hash k in
        let vh = ValueMeta.hash v in
        acc lxor vh lxor (kh lsl (1 land vh))
      ) m (length m)

  let equal (m1 : t) (m2 : t) : bool =
    fold_short_circuit m1 (length m1 <> length m2) false (fun k v acc ->
        match H.find_opt m2 k with
        | Some v' -> ValueMeta.equal v' v
        | None -> false
      )

  (* optimized for case where maps are rarely equal *)
  let equal_with_hash (m1 : t) (m2 : t) : bool =
    if length m1 <> length m2 || hash m1 <> hash m2 then
      false
    else
      fold_short_circuit m1 true false (fun k v acc ->
          match H.find_opt m2 k with
          | Some v' -> ValueMeta.equal v' v
          | None -> false
        )

  let exists (m : t) (f : KeyMeta.t -> ValueMeta.t -> bool) : bool =
    fold_short_circuit m false true (fun k v _ ->
        f k v
      )

  (*
  let add_unique (m : t) (k : KeyMeta.t) (v : ValueMeta.t) : unit =
    (* TODO check which structure is used where how and how often *)

  let mapped_inplace (m : t) (f : KeyMeta.t -> ValueMeta.t -> ValueMeta.t) : t =
    let m' = copy m in
    filter_map_inplace (fun 
*)

  let to_list (m : t) : (KeyMeta.t * ValueMeta.t) list = List.of_seq @@ H.to_seq m

  let of_list (l : (KeyMeta.t * ValueMeta.t) list) : t = H.of_seq @@ List.to_seq l
end

(*
let nt_ty_hash (nt, ty : nt_id * ty) : int = Hashtbl.hash (nt, id_of_ty ty)

let nt_ty_eq (nt1, ty1 : nt_id * ty) (nt2, ty2 : nt_id * ty) : bool =
  nt1 = nt2 && eq_ty ty1 ty2

module NTTyMap = HashMap.Make (struct
    type t = nt_id * ty
    let hash = nt_ty_hash
    let equal = nt_ty_eq
  end) (struct
    type t = bool
    let hash = Hashtbl.hash
    let equal = (=)
  end)

(** Map from used nonterminal typings to whether they were used twice or more. *)
type used_nts = NTTyMap.t

let singleton_used_nts (nt_ty : nt_id * ty) : used_nts =
  let used_nts = NTTyMap.empty () in
  NTTyMap.add used_nts nt_ty false;
  used_nts
*)

(*
(** Environment metadata. *)
type env_meta = { dup : bool; pr_arg : bool; used_nts : used_nts; positive : bool }

let empty_env_meta : env_meta =
  { dup = false; pr_arg = false; used_nts = NTTyMap.empty; positive = false }
*)

(*
  include HashMap.Make (struct
      type t = env
      let hash = env_hash
      let equal = env_eq
    end) (struct
      type t = env_meta
      let hash meta =
        Hashtbl.hash (meta.dup, meta.pr_arg, meta.positive, NTTyMap.hash meta.used_nts)
      let equal meta1 meta2 =
        meta1.dup = meta2.dup &&
        meta1.pr_arg = meta2.pr_arg &&
        meta1.positive = meta2.positive &&
        NTTyMap.equal meta1.used_nts meta2.used_nts
    end)
*)
