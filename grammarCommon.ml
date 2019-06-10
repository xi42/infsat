(** Identifier of a nonterminal. Nonterminals are numbered starting from 0. **)
type nt_id = int

(** Identifier of a variable. Contains identifier of the nonterminal it is defined in and its
    index *)
type var_id = nt_id * int

type terminal = A | B | E | T

module SortedVars = SortedList.Make(struct
    type t = var_id
    let compare = Pervasives.compare
  end)

type vars = SortedVars.t

module SortedNTs = SortedList.Make(struct
    type t = nt_id
    let compare = Pervasives.compare
  end)

type nts = SortedNTs.t

let arity_of_terminal (a : terminal) : int =
  match a with
  | A -> 1
  | B -> 2
  | E -> 0
  | T -> 2

let string_of_terminal (a : terminal) : string =
  match a with
  | A -> "a"
  | B -> "b"
  | E -> "e"
  | T -> "t"

(* computed sorts of terms *)
type sort = SFun of sort * sort | SAtom

let sort_of_terminal (a : terminal) : sort =
  match a with
  | A -> SFun (SAtom, SAtom)
  | B -> SFun (SAtom, SFun (SAtom, SAtom))
  | E -> SAtom
  | T -> SFun (SAtom, SFun (SAtom, SAtom))

let rec string_of_sort : sort -> string = function
  | SAtom -> "o"
  | SFun (s1, s2) -> "(" ^ string_of_sort s1 ^ ") -> " ^ string_of_sort s2
