type nt_id = int (** names of non-terminal symbols; they are just integers **)
type var_id = nt_id * int (* pair of the non-terminal and the variable index *)

module SortedVars = SortedList.Make(struct
    type t = var_id
    let compare = Pervasives.compare
  end)

module SortedNTs = SortedList.Make(struct
    type t = nt_id
    let compare = Pervasives.compare
  end)
