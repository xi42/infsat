type 'a binding_elt = int * int * 'a

(** Binding is information what flows into which arguments in the form of a list with elements
    (i, j, x) for range of arguments on positions i-j. x can be, e.g., hterms_id or list of
    types. Note that bindings are not ordered. *)
type 'a binding = 'a binding_elt list

let string_of_binding (string_of_a : 'a -> string) (b : 'a binding) : string =
  "[" ^
  String.concat "; " (
    List.map (fun (i, j, a) ->
        "(" ^ string_of_int i ^ ", " ^ string_of_int j ^ ", " ^ string_of_a a ^ ")"
      ) b
  ) ^
  "]"
