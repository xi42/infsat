open Environment
open Type

(** Environment with metadata - whether a duplication occured and whether a productive
    actual argument was used when computing a given environment. *)
type envm = { env : env; dup : bool; pr_arg : bool }

let mk_envm (env : env) : envm = { env = env; dup = false; pr_arg = false }

let string_of_envm (envm : envm) : string =
  let dup_info = if envm.dup then " DUP" else "" in
  let pr_arg_info = if envm.pr_arg then " PR_ARG" else "" in
  envm.env#to_string ^ dup_info ^ pr_arg_info

(** A sorted list of environments and information whether a duplication occured when computing
    them. In other words, list of possible typings of variables delimited by ANDs, treated as
    if there was OR as the delimiter. *)
module EnvList = struct
  include SortedList.Make(struct
      type t = envm
      let compare envm1 envm2 =
        Utilities.compare_pair env_compare Pervasives.compare
          (envm1.env, (envm1.dup, envm1.pr_arg)) (envm2.env, (envm2.dup, envm2.pr_arg))
    end)

  (** Conversion of list of envs to an envl assuming default flags. *)
  let of_list_default_flags (l : env list) : t =
    of_list @@ List.map (fun env -> mk_envm env) l

  (** Returns the same envl with flags set to default values. *)
  let with_default_flags (envl : t) : t =
    filter_duplicates @@ map_monotonic (fun envm -> mk_envm envm.env) envl

  let to_string (envl : t) : string =
    String.concat " \\/ " @@ map string_of_envm envl
end

type envl = EnvList.t

(** A base module for TargetEnvlList.
    Based on SortedList, but compare would incorrectly merge two different elements with the
    same keys, so this module should not be used directly and is dependent on implementation
    details of SortedList. *)
module TargetEnvlListBase = SortedList.Make(struct
    type t = ty * EnvList.t
    let compare (k1, _) (k2, _) = Ty.compare k1 k2
  end)

(** A map from targets to environments under which they occur with duplication information. *)
module TargetEnvl = struct
  type t = TargetEnvlListBase.t

  (** Empty TEL. *)
  let empty : t = TargetEnvlListBase.empty

  (** Singleton TEL with mapping from target to env with no duplication *)
  let singleton (target : ty) (env : env) =
    TargetEnvlListBase.singleton (target, EnvList.singleton @@ mk_envm env)

  let of_list (l : (ty * envm list) list) : t =
    TargetEnvlListBase.of_list @@ List.map (fun (target, envl) ->
        (target, EnvList.of_list envl)) l

  (** Conversion of list of pairs target-envl to respective tel assuming default flags. *)
  let of_list_default_flags (l : (ty * env list) list) : t =
    TargetEnvlListBase.of_list @@ (l |> List.map (fun (target, envl) ->
        (target, EnvList.of_list_default_flags envl)))

  let to_list : t -> (ty * envm list) list =
    TargetEnvlListBase.map (fun (target, envl) -> (target, EnvList.to_list envl))

  let mem (tel : t) (target : ty) : bool =
    tel |> TargetEnvlListBase.exists (fun (target', _) -> Ty.compare target target' = 0)

  let is_empty (tel : t) : bool = TargetEnvlListBase.is_empty tel

  let size : t -> int =
    TargetEnvlListBase.fold_left (fun acc (_, envl) -> acc + EnvList.length envl) 0

  let merge : t -> t -> t =
    TargetEnvlListBase.merge_custom
      (fun (target1, envl1) (_, envl2) -> (target1, EnvList.merge envl1 envl2))

  let for_all (f : ty -> envm -> bool) (tel : t) : bool =
    tel |> TargetEnvlListBase.for_all (fun (target, envl) ->
        envl |> EnvList.for_all (fun envm -> f target envm))

  let exists (f : ty -> envm -> bool) (tel : t) : bool =
    tel |> TargetEnvlListBase.exists (fun (target, envl) ->
        envl |> EnvList.exists (fun envm -> f target envm))

  (** Removes targets with empty list of envms. *)
  let remove_empty_targets : t -> t =
    TargetEnvlListBase.filter (fun (target, envl) -> not @@ EnvList.is_empty envl)

  (** Returns TEL with flags of environments set to default values and removes duplicates. *)
  let with_default_flags (tel : t) : t =
    tel |> TargetEnvlListBase.map_monotonic (fun (target, envl) ->
        (target, EnvList.with_default_flags envl)
      )

  (** Changes target of the sole element of TEL. Requires TEL to have exactly one target.
      Also removes duplication flag and sets productive actual argument flag to whether previous
      target was productive. *)
  let retarget (target : ty) (tel : t) : t =
    assert (TargetEnvlListBase.length tel <= 1);
    tel |> TargetEnvlListBase.map_monotonic (fun (target', envl) ->
        (target, EnvList.filter_duplicates (envl |>EnvList.map_monotonic (fun envm -> {
               envm with dup = false; pr_arg = is_productive target'
             })))
      )

  (** Returns filtered TEL with only the environments that have no duplication for nonproductive
      targets. *)
  let filter_no_dup_for_np_targets (tel : t) : t =
    remove_empty_targets @@ TargetEnvlListBase.map_monotonic (fun (target, envl) ->
        if is_productive target then
          (target, envl)
        else
          (target, EnvList.filter (fun envm -> not envm.dup) envl)
      ) tel

  (** Returns filtered TEL with only the environments that have a duplication for productive
      targets. *)
  let filter_dup_or_pr_arg_for_pr_targets (tel : t) : t =
    remove_empty_targets @@ TargetEnvlListBase.map_monotonic (fun (target, envl) ->
        if is_productive target then
          (target, EnvList.filter (fun envm -> envm.dup || envm.pr_arg) envl)
        else
          (target, envl)
      ) tel

  (** Returns filtered TEL with only the environments that contain productive_vars. *)
  let filter_pr_vars (tel : t) : t =
    remove_empty_targets @@ TargetEnvlListBase.map_monotonic (fun (target, envl) ->
        (target, EnvList.filter (fun envm -> envm.env#has_pr_vars) envl)
      ) tel

  (** Flatten an intersection of variable environment lists, intersected separately for each target.
      Environment lists are essentially OR-separated lists of AND-separated lists of typings of
      unique in inner list variables. Flattening means moving outer intersection (AND) inside. *)
  let intersect (tel1 : t) (tel2 : t) : t =
    (* separately for each target *)
    (* TODO intersect or merge? *)
    TargetEnvlListBase.intersect_custom (fun (target1, envl1) (_, envl2) ->
        (* for each env1 in envs in tel1 *)
        let merged_envl = EnvList.fold_left (fun acc envm1 ->
            (* for each env2 in envs in tel2 *)
            EnvList.filter_duplicates @@
            EnvList.of_list @@
            EnvList.map (fun envm2 ->
                (* merge them together, compute duplication, and reshape the list result into
                   a TEL *)
                let env, merge_dup = envm1.env#merge envm2.env in
                { env = env;
                  dup = envm1.dup || envm2.dup || merge_dup;
                  pr_arg = envm1.pr_arg || envm2.pr_arg }
              ) envl2
          ) EnvList.empty envl1
        in
        (target1, merged_envl)
      ) tel1 tel2

  let map (f : ty -> envl -> 'a) (tel : t) : 'a list =
    TargetEnvlListBase.map (fun (target, envl) -> f target envl) tel

  let targets (tel : t) : ity =
    TyList.of_list @@ TargetEnvlListBase.map fst tel

  let targets_count (tel : t) : int =
    TargetEnvlListBase.length tel

  let to_fun_ity (tel : t) : ity =
    TyList.of_list @@ TargetEnvlListBase.fold_left (fun acc (target, envl) ->
        EnvList.fold_left (fun acc envm ->
            envm.env#mk_fun target :: acc
          ) acc envl
      ) [] tel

  let compare : t -> t -> int =
    TargetEnvlListBase.compare_custom @@ Utilities.compare_pair Ty.compare EnvList.compare

  let equal (tel1 : t) (tel2 : t) : bool = compare tel1 tel2 = 0

  let to_string (tel : t) =
    Utilities.string_of_list Utilities.id @@
    TargetEnvlListBase.map (fun (target, envl) ->
        string_of_ty target ^ " => " ^ EnvList.to_string envl
      ) tel
end

(** target -> environment list map *)
type tel = TargetEnvl.t
