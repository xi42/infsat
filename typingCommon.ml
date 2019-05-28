open GrammarCommon
open HGrammar
open Type

type nt_ty = nt_id * ty

let nt_ty_compare : nt_ty -> nt_ty -> int =
  Utilities.compare_pair Pervasives.compare Ty.compare

let nt_ty_eq (nt1, ty1 : nt_ty) (nt2, ty2 : nt_ty) : bool =
  nt1 = nt2 && Ty.equal ty1 ty2

let string_of_nt_ty (nt, ty : nt_ty) : string =
  string_of_int nt ^ " : " ^ string_of_ty ty

module NTTyMap = struct
  include Map.Make (struct
      type t = nt_id * ty
      let compare = nt_ty_compare
    end)

  let of_list (l : (key * 'a) list) : 'a t = of_seq @@ List.to_seq l
end

module NTTySet = struct
  include Set.Make (struct
      type t = nt_ty
      let compare = nt_ty_compare
    end)

  let set_of_map_keys (m : 'a NTTyMap.t) : t =
    of_seq @@ Seq.map fst @@ NTTyMap.to_seq m
end

type t_ty = terminal * ty

let string_of_t_ty (t, ty : t_ty) : string =
  string_of_terminal t ^ " : " ^ string_of_ty ty

module TTyMap =
  Map.Make (struct
    type t = t_ty
    let compare = Utilities.compare_pair Pervasives.compare Ty.compare
  end)
