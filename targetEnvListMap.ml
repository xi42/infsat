open Environment
open Type

(** Environment with metadata - whether a duplication occured and whether a productive
    actual argument was used when computing a given environment. *)
type envm = { env : env; dup : bool; pr_arg : bool }

let mk_envm (env : env) : envm = { env = env; dup = false; pr_arg = false }

(** A sorted list of environments and information whether a duplication occured when computing
    them. *)
module EnvList = SortedList.Make(struct
    type t = envm
    let compare envm1 envm2 =
      Utilities.compare_pair env_compare Pervasives.compare
        (envm1.env, (envm1.dup, envm1.pr_arg)) (envm2.env, (envm2.dup, envm2.pr_arg))
  end)

(** A map from targets to environments under which they occur with duplication information. *)
module TargetEnvlList = SortedList.Make(struct
    type t = ty * EnvList.t
    let compare (k1, _) (k2, _) = Ty.compare k1 k2
  end)

(** target -> environment list map *)
type telm = TargetEnvlList.t

(** Empty TELM. *)
let empty : telm = TargetEnvlList.empty

(** Singleton TELM with mapping from target to env with no duplication *)
let singleton (target : ty) (env : env) =
  TargetEnvlList.singleton (target, EnvList.singleton @@ mk_envm env)

let of_list (l : (ty * envm list) list) : telm =
  TargetEnvlList.of_list @@ List.map (fun (target, envl) ->
      (target, EnvList.of_list envl)) l

(** Conversion of list of pairs target-envl to respective telm assuming default flags. *)
let of_list_default_flags (l : (ty * envl) list) : telm =
  TargetEnvlList.of_list @@ List.map (fun (target, envl) ->
      (target, EnvList.of_list @@ List.map (fun env -> mk_envm env) envl)) l

let to_list : telm -> (ty * envm list) list =
  TargetEnvlList.map (fun (target, envl) -> (target, EnvList.to_list envl))

let mem (telm : telm) (target : ty) : bool =
  telm |> TargetEnvlList.exists (fun (target', _) -> Ty.compare target target' = 0)

let is_empty (telm : telm) : bool = TargetEnvlList.is_empty telm

let size : telm -> int =
  TargetEnvlList.fold_left (fun acc (_, envl) -> acc + EnvList.length envl) 0

let merge : telm -> telm -> telm =
  TargetEnvlList.merge_custom
    (fun (target1, envl1) (_, envl2) -> (target1, EnvList.merge envl1 envl2))
        
let for_all (f : ty -> envm -> bool) (telm : telm) : bool =
  telm |> TargetEnvlList.for_all (fun (target, envl) ->
      envl |> EnvList.for_all (fun envm -> f target envm))
                    
let exists (f : ty -> envm -> bool) (telm : telm) : bool =
  telm |> TargetEnvlList.exists (fun (target, envl) ->
      envl |> EnvList.exists (fun envm -> f target envm))

(** Removes targets with empty list of envms. *)
let remove_empty_targets : telm -> telm =
  TargetEnvlList.filter (fun (target, envl) -> not @@ EnvList.is_empty envl)

(** Returns TELM with flags of environments set to default values and removes duplicates. *)
let with_default_flags (telm : telm) : telm =
  telm |> TargetEnvlList.map_monotonic (fun (target, envl) ->
      (target, envl |> EnvList.map_monotonic_and_filter_duplicates (fun envm -> {
             envm with dup = false; pr_arg = false
           }))
    )
  
(** Changes target of the sole element of TELM. Requires TELM to have exactly one target.
    Also removes duplication flag and sets productive actual argument flag to whether previous
    target was productive. *)
let retarget (target : ty) (telm : telm) : telm =
  assert (TargetEnvlList.length telm <= 1);
  telm |> TargetEnvlList.map_monotonic (fun (target', envl) ->
      (target, envl |> EnvList.map_monotonic_and_filter_duplicates (fun envm -> {
             envm with dup = false; pr_arg = is_productive target'
           }))
    )

(** Returns filtered TELM with only the environments that have no duplication for nonproductive
    targets. *)
let filter_no_dup_for_np_targets (telm : telm) : telm =
  remove_empty_targets @@ TargetEnvlList.map_monotonic (fun (target, envl) ->
      if is_productive target then
        (target, envl)
      else
        (target, EnvList.filter (fun envm -> not envm.dup) envl)
    ) telm

(** Returns filtered TELM with only the environments that have a duplication for productive
    targets. *)
let filter_dup_or_pr_arg_for_pr_targets (telm : telm) : telm =
  remove_empty_targets @@ TargetEnvlList.map_monotonic (fun (target, envl) ->
      if is_productive target then
        (target, EnvList.filter (fun envm -> envm.dup || envm.pr_arg) envl)
      else
        (target, envl)
    ) telm

(** Returns filtered TELM with only the environments that contain productive_vars. *)
let filter_pr_vars (telm : telm) : telm =
  remove_empty_targets @@ TargetEnvlList.map_monotonic (fun (target, envl) ->
      (target, EnvList.filter (fun envm -> envm.env#has_pr_vars) envl)
    ) telm

(** Flatten an intersection of variable environment lists, intersected separately for each target.
    Environment lists are essentially OR-separated lists of AND-separated lists of typings of
    unique in inner list variables. Flattening means moving outer intersection (AND) inside. *)
let intersect (telm1 : telm) (telm2 : telm) : telm =
  (* separately for each target *)
  TargetEnvlList.merge_custom (fun (target1, envl1) (_, envl2) ->
      (* for each env1 in envs in telm1 *)
      let merged_envl = EnvList.fold_left (fun acc envm1 ->
          (* for each env2 in envs in telm2 *)
          EnvList.of_list @@
          EnvList.map (fun envm2 ->
              (* merge them together, compute duplication, and reshape the list result into
                 a TELM *)
              let env, merge_dup = envm1.env#merge envm2.env in
              { env = env;
                dup = envm1.dup || envm2.dup || merge_dup;
                pr_arg = envm1.pr_arg || envm2.pr_arg }
            ) envl2
        ) EnvList.empty envl1
      in
      (target1, merged_envl)
    ) telm1 telm2

let telm_compare : telm -> telm -> int =
  TargetEnvlList.compare_custom @@ Utilities.compare_pair Ty.compare EnvList.compare

let telm_eq (telm1 : telm) (telm2 : telm) : bool = telm_compare telm1 telm2 = 0

let to_string (telm : telm) =
  Utilities.string_of_list Utilities.id @@
  TargetEnvlList.map (fun (target, envl) ->
      string_of_ty target ^ " => " ^ String.concat " | " @@
      EnvList.map (fun envm ->
          let dup_info = if envm.dup then "+" else "" in
          let pr_arg_info = if envm.pr_arg then "*" else "" in
          envm.env#to_string ^ dup_info ^ pr_arg_info
        ) envl
    ) telm
