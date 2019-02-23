type 'a binding_elt = int * int * 'a

(** Binding is information what flows into which arguments in the form of a list with elements
    (i, j, x) for range of arguments on positions i-j. x can be, e.g., hterms_id or list of
    types. *)
type 'a binding = 'a binding_elt list

let string_of_binding (string_of_a : 'a -> string) (b : 'a binding) : string =
  "[" ^
  String.concat "; " (
    List.map (fun (i, j, a) ->
        "(" ^ string_of_int i ^ ", " ^ string_of_int j ^ ", " ^ string_of_a a ^ ")"
      ) b
  ) ^
  "]"

let rec binding_compare (a_compare : 'a -> 'a -> int) (b1 : 'a binding) (b2 : 'a binding) : int =
  match b1, b2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | (i1, j1, a1) :: b1', (i2, j2, a2) :: b2' ->
    let ci = Pervasives.compare i1 i2 in
    if ci <> 0 then
      ci
    else
      let cj = Pervasives.compare j1 j2 in
      if cj <> 0 then
        cj
      else
        let ca = a_compare a1 a2 in
        if ca <> 0 then
          ca
        else
          binding_compare a_compare b1' b2'
