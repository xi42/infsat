open GrammarCommon
open Type

(* --- pure environment --- *)

(** A single possible typing of variables mapping variables to their types, treated as if there
    was AND as the delimiter. *)
module Env = struct
  include SortedList.Make(struct
    type t = var_id * ity
    let compare (id1, _) (id2, _) = Pervasives.compare id1 id2
  end)

  (** Merge works differently here, since types are not part of the compare function and need to
      be merged manually. Also, information about duplication of productive variables is needed. *)
  let merge_with_dup_info v1 v2 : t * bool =
    let dup = ref false in
    let res = merge_custom (fun (id1, ity1) (_, ity2) ->
        let merged_ity = TyList.merge_custom (fun ty _ ->
            if is_productive ty then
              dup := true;
            ty
          ) ity1 ity2
        in
        (id1, merged_ity)
      ) v1 v2
    in
    (res, !dup)

  let merge v1 v2 = fst @@ merge_with_dup_info v1 v2
end

type env = Env.t

(** List of possible typings of variables, treated as if there was OR as the delimiter. *)
type envl = env list

let string_of_env : env -> string =
  Env.to_string (fun ((nt, vix), ity) ->
      string_of_int nt ^ "-" ^ string_of_int vix ^ " : " ^ string_of_ity ity
    )

let string_of_envl (envl : envl) : string =
  Utilities.string_of_list string_of_env envl

(** List of variable environments does not need to be sorted during computations, but it is useful
    for unique representation when testing. *)
let sort_envl (envl : envl) : envl =
  List.sort (Env.compare_custom (fun (id1, ity1) (id2, ity2) ->
      let res = Pervasives.compare id1 id2 in
      if res = 0 then
        TyList.compare ity1 ity2
      else
        res
    )) envl

(* --- environment with flags --- *)

(** Variable environment along with flags whether there was a duplication during its
    construction and whether a productive argument was used. *)
type envf = env * bool * bool

(** List of variable environments with duplication flags. *)
type envfl = envf list

(** Merges vtes (variable types) by combining the list of type bindings in order, and combining
    types when a binding for the same variable is present in both lists. The resulting binding
    is ordered ascendingly lexicographically by variable ids. Combining types is also idempodently
    merging list of types (i.e., there are sets of types). TODO redo docs from old ones *)
let intersect_two_envs (env1, dup1, pruse1 : envf) (env2, dup2, pruse2 : envf) : envf =
  let intersection, dup = Env.merge_with_dup_info env1 env2 in
  (intersection, dup1 || dup2 || dup, pruse1 || pruse2)

(** Flatten an intersection of variable environment lists, which are OR-separated lists of
    AND-separated lists of typings of unique in inner list variables. Flattening means moving
    outer intersection (AND) inside. Return if there was a duplication. *)
let rec intersect_two_envfls (envl1 : envfl) (envl2 : envfl) : envfl =
  match envl1, envl2 with
  | _, [] -> [] (* second typing is invalid *)
  | [], _-> [] (* first typing is invalid *)
  | _ ->
    List.fold_left
      (fun acc env1 ->
         let envl2' = List.rev_map (fun env2 ->
             intersect_two_envs env1 env2
           ) envl2
         in
         List.rev_append envl2' acc)
      [] envl1
