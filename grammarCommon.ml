type nt_id = int (** names of non-terminal symbols; they are just integers **)
type var_id = nt_id * int (* pair of the non-terminal and the variable index *)

type terminal = A | B | E

module SortedVars = SortedList.Make(struct
    type t = var_id
    let compare = Pervasives.compare
  end)

module SortedNTs = SortedList.Make(struct
    type t = nt_id
    let compare = Pervasives.compare
  end)

let arity_of_terminal (a : terminal) : int =
  match a with
  | A -> 1
  | B -> 2
  | E -> 0

let string_of_terminal (a : terminal) : string =
  match a with
  | A -> "a"
  | B -> "b"
  | E -> "e"
