open Binding
open GrammarCommon
open Type

(* --- pure environment --- *)

(** A single possible typing of variables mapping variables to their types, treated as if there
    was AND as the delimiter.
    This structure satisfies the following desired properties:
    - has O(1) access to ity of given var
    - has O(n) merge with another environment *)
class env (var_itys : ity array) = object(self)
  (* --- access --- *)

  method var_count : int = Array.length var_itys

  method get_var_itys : ity array = var_itys

  method get_var_ity (_, i : var_id) : ity = var_itys.(i)

  method mem (v : var_id) (ty : ty) : bool =
    TyList.mem ty @@ self#get_var_ity v

  method compare (env' : env) : int =
    let var_itys' = env'#get_var_itys in
    assert (Array.length var_itys = Array.length var_itys');
    let rec compare_aux (i : int) =
      if i = Array.length var_itys then
        0
      else
        let ci = TyList.compare var_itys.(i) var_itys'.(i) in
        if ci <> 0 then
          ci
        else
          compare_aux (i + 1)
    in
    compare_aux 0

  method has_productive_vars : bool =
    Array.exists (fun ity -> TyList.exists is_productive ity) var_itys

  (* --- manipulation --- *)

  method set_var_ity (i : int) (ity : ity) =
    var_itys.(i) <- ity
  
  (** Merging environments is summation of itys of the same var. The result is a new, merged
      environment and information whether duplication of a productive variable occured. *)
  method merge (env' : env) : env * bool =
    let var_itys' = env'#get_var_itys in
    assert (Array.length var_itys = Array.length var_itys');
    let var_itys_new = Array.make (Array.length var_itys) TyList.empty in
    let dup = ref false in
    Array.iteri (fun i ity ->
        var_itys_new.(i) <- TyList.merge_custom (fun ty _ ->
            if is_productive ty then
              dup := true;
            ty
          ) ity var_itys'.(i)
      ) var_itys;
    (new env @@ var_itys_new, !dup)

  (* --- printing --- *)
  
  method to_string : string =
    String.concat ", " @@
    List.mapi (fun i ity -> string_of_int i ^ " : " ^ string_of_ity ity) @@
    Array.to_list var_itys
end

let empty_env (var_count : int) : env =
  new env @@ Array.make var_count TyList.empty

let singleton_env (var_count : int) (_, i : var_id) (ity : ity) : env =
  let env = empty_env var_count in
  env#set_var_ity i ity;
  env

let hty_binding2env (var_count : int) (binding : hty binding) : env =
  let itys = Array.make var_count TyList.empty in
  List.iter (fun (i, _, hty) ->
      List.iteri (fun ix ity ->
          itys.(i + ix) <- ity
        ) hty
    ) binding;
  new env itys

(** List of possible typings of variables, treated as if there was OR as the delimiter. *)
type envl = env list

let env_compare (env1 : env) (env2 : env) : int = env1#compare env2

let envl_compare : envl -> envl -> int =
  Utilities.compare_lists env_compare

let envl_eq (envl1 : envl) (envl2 : envl) : bool =
  envl_compare envl1 envl2 = 0

let string_of_envl (envl : envl) : string =
  Utilities.string_of_list (fun env -> env#to_string) envl

(* --- environment with flags --- *)

(** Variable environment along with flags whether there was a duplication during its
    construction and whether a productive argument was used. *)
type envf = env * bool * bool

(** List of variable environments with duplication flags. *)
type envfl = envf list

(** Merges two environments into one and returns it along with merged flags. None of the arguments
    are modified. *)
let intersect_two_envs (env1, dup1, pruse1 : envf) (env2, dup2, pruse2 : envf) : envf =
  let env, merge_dup = env1#merge env2 in
  (env, dup1 || dup2 || merge_dup, pruse1 || pruse2)

(** Flatten an intersection of variable environment lists, which are OR-separated lists of
    AND-separated lists of typings of unique in inner list variables. Flattening means moving
    outer intersection (AND) inside. The operations are done on environments with flags and
    the arguments are not modified. *)
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
