open HGrammar
open Utilities

type 'a binding_elt = int * int * 'a

(** Binding is information what flows into which arguments in the form of a list with elements
    (i, j, x) for range of arguments on positions i-j. x can be, e.g., hterms_id or list of
    types. Note that bindings are not ordered. *)
type 'a binding = 'a binding_elt list

type bix = int

(** Constructs a map from variable position to index in a binding that contains that position. *)
let var_bix (b : 'a binding) : (bix * int) IntMap.t =
  List.fold_left (fun acc (ix, (i, j, _)) ->
      List.fold_left (fun acc v ->
          IntMap.add v (ix, v - i) acc
        ) acc @@ range i (j + 1)
    ) IntMap.empty @@ index_list b

let rec find_bound (b : 'a binding) (v : int) : 'a =
  match b with
  | [] -> failwith @@ "Did not find " ^ string_of_int v ^ " in the binding."
  | (i, j, a) :: b' ->
    if i <= v && v <= j then
      a
    else
      find_bound b' v

let string_of_binding (string_of_a : 'a -> string) (b : 'a binding) : string =
  "[" ^
  String.concat "; " (
    List.map (fun (i, j, a) ->
        "(" ^ string_of_int i ^ ", " ^ string_of_int j ^ ", " ^ string_of_a a ^ ")"
      ) b
  ) ^
  "]"
