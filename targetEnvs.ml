open Context
open Environment
open GrammarCommon
open HGrammar
open Type
open TypingCommon
open Utilities

(** A set of environments and information whether a duplication occured when computing
    them. In other words, list of possible typings of variables delimited by ANDs, treated as
    if there was OR as the delimiter. *)
module ContextEnvs = struct
  include Set.Make (struct
      type t = env * ctx
      let compare =
        compare_pair env_compare ctx_compare
    end)

  (** Returns the same envs with flags set to default values. *)
  let with_empty_temp_flags_and_locs (envs : t) : t =
    map (fun (env, ctx) ->
        let e = {
          env with dup = false; pr_arg = false; loc_types = empty_loc_types
        } in
      (e, ctx)) envs

  let to_string (envs : t) : string =
    "(" ^ (
      concat_map " \\/ " (fun (env, ctx) -> string_of_env env ^ " CTX " ^ string_of_ctx ctx) @@
      elements envs) ^
    ")"
end

type cenvs = ContextEnvs.t

(** A map from targets to environments under which they occur with typing metadata. *)
module TargetEnvs = struct
  type t = cenvs TyMap.t

  (** Empty TE. *)
  let empty : t = TyMap.empty

  (** Singleton TE with mapping from target to env. *)
  let singleton_of_env (target : ty) (env : env) (ctx : ctx) : t =
    TyMap.singleton target @@ ContextEnvs.singleton (env, ctx)

  (** Singleton TE with mapping from target to env with no duplication. For testing purposes. *)
  let singleton_empty_meta (target : ty) (vars : (int * ity) list) (ctx : ctx) : t =
    singleton_of_env target (mk_env_empty_meta @@ IntMap.of_list vars) ctx

  let union : t -> t -> t =
    TyMap.union (fun target envs1 envs2 ->
        Some (ContextEnvs.union envs1 envs2)
      )

  let of_list (l : (ty * (env * ctx) list) list) : t =
    List.fold_left (fun acc (target, envs) ->
        TyMap.update target (fun envs' ->
            match envs' with
            | Some envs' -> Some (ContextEnvs.union envs envs')
            | None -> Some envs
          ) acc
      ) empty @@
    List.map (fun (target, envs) ->
        (target, ContextEnvs.of_list envs)) @@
    l

  (** Conversion of list of pairs target-envs to respective TE assuming default flags and
      no location info. For testing purposes. *)
  let of_list_empty_flags_empty_meta (l : (ty * ((int * ity) list * ctx) list) list) : t =
    of_list @@ (l |> List.map (fun (target, cvars) ->
        (target, cvars |> List.map (fun (vars, ctx) ->
             (mk_env_empty_meta @@ IntMap.of_list vars, ctx)
           ))))
      
  let to_list (te : t) : (ty * (env * ctx) list) list =
    List.map (fun (target, envs) -> (target, ContextEnvs.elements envs)) @@ TyMap.bindings te

  let mem (te : t) (target : ty) : bool =
    TyMap.mem target te

  let is_empty : t -> bool = TyMap.is_empty

  let size (te : t) : int =
    TyMap.fold (fun _ envs acc -> acc + ContextEnvs.cardinal envs) te 0

  let targets (te : t) : ty list =
    List.map fst @@ TyMap.bindings te

  (** Removes targets with empty list of envs. *)
  let remove_empty_targets : t -> t =
    TyMap.filter (fun target envs -> not @@ ContextEnvs.is_empty envs)

  (** Returns TE with flags of environments set to default values and removes duplicates. *)
  let with_empty_temp_flags_and_locs : t -> t =
    TyMap.map ContextEnvs.with_empty_temp_flags_and_locs

  (** Changes target of the sole element of TE. Requires TE to have exactly one target.
      Also removes duplication flag and sets productive actual argument flag to whether previous
      target was productive. *)
  let retarget (target : ty) (te : t) : t =
    assert (TyMap.cardinal te <= 1);
    TyMap.of_seq @@
    Seq.map (fun (target', envs') ->
        let envs =
          envs' |> ContextEnvs.map (fun (env, ctx) ->
              (* note this does not touch used_nts and positive so that information is
                 carried over *)
              ({ env with dup = false; pr_arg = is_productive target' }, ctx)
            )
        in
        (target, envs)
      ) @@
    TyMap.to_seq te

  (** Construct a TE with all data for targets that satisfy condition f. *)
  let filter_targets (f : ty -> bool) (te : t) : t =
    TyMap.filter (fun ty _ -> f ty) te
  
  (** Returns filtered TE with only the environments that have no duplication for nonproductive
      targets. *)
  let filter_no_dup_for_np_targets (te : t) : t =
    remove_empty_targets @@ TyMap.mapi (fun target envs ->
        if is_productive target then
          envs
        else
          ContextEnvs.filter (fun (env, _) -> not env.dup) envs
      ) te

  (** Returns filtered TE with only the environments that have a duplication for productive
      targets. *)
  let filter_dup_or_pr_arg_for_pr_targets (te : t) : t =
    remove_empty_targets @@ TyMap.mapi (fun target envs ->
        if is_productive target then
          ContextEnvs.filter (fun (env, _) -> env.dup || env.pr_arg) envs
        else
          envs
      ) te

  (** Returns filtered TE with only the environments that contain productive_vars. *)
  let filter_pr_vars (te : t) : t =
    remove_empty_targets @@ TyMap.mapi (fun target envs ->
        ContextEnvs.filter (fun (env, _) -> env_has_pr_vars env) envs
      ) te

  let filter_satisfied_ctx (te : t) : t =
    remove_empty_targets @@ TyMap.mapi (fun target envs ->
        ContextEnvs.filter (fun (_, ctx) -> ctx_requirements_satisfied ctx) envs
      ) te

  (** Flatten an intersection of variable environments, intersected separately for each target.
      Environments are essentially OR-separated sets of AND-separated sets of typings of
      variables with contexts. Flattening means moving outer intersection (AND) inside.
      AND of two environments is just summing all restrictions, i.e., intersecting intersection
      types. Intersection of contexts is intersection of product with additional border cases
      with hterms/nonterminal typing restrictions. *)
  let intersect (te1 : t) (te2 : t) : t =
    (* separately for each target *)
    remove_empty_targets @@
    TyMap.merge (fun target envs1 envs2 ->
        match envs1, envs2 with
        | Some envs1, Some envs2 ->
          Some (
            (* for each env in envs in te1 *)
            ContextEnvs.fold (fun (env1, ctx1) acc ->
                (* for each env in envs in te2 *)
                ContextEnvs.fold (fun (env2, ctx2) acc ->
                    (* Merge them together, compute duplication, and reshape the list result into
                       a TE. This is the only place where duplication flag is set. If there was a
                       duplication, positive flag is updated to true too. *)
                    match intersect_ctxs ctx1 ctx2 with
                    | Some ctx ->
                      ContextEnvs.add (intersect_envs env1 env2, ctx) acc
                    | None -> acc
                  ) envs2 acc
              ) envs1 ContextEnvs.empty
          )
        | _, _ -> None
      ) te1 te2

  (** Returns the types of arguments to which terms typed as targets can be applied in
      variable environments of the target. This makes sense for hterms where the type is not
      forced. *)
  let targets_as_args (te : t) : ity =
    TyList.remove_duplicates @@ TyList.of_list @@
    TyMap.fold (fun target envs acc ->
        if is_productive target then
          target :: acc
        else
          (* assuming all listed targets have non-empty environments *)
          let (some_env, some_ctx) = ContextEnvs.choose envs in
          if env_has_pr_vars some_env then
            if ContextEnvs.for_all (fun (env, _) -> env_has_pr_vars env) envs then
              with_productivity true target :: acc
            else
              with_productivity true target :: target :: acc
          else if ContextEnvs.exists (fun (env, _) -> env_has_pr_vars env) envs then
            with_productivity true target :: target :: acc
          else
            target :: acc
      ) te []

  let targets_count : t -> int = TyMap.cardinal

  (** Creates function types from targets and variables in their environments and iterates over
      all resulting function types along with environment. *)
  let iter_fun_ty (arity : int) (f : ty -> env -> unit) : t -> unit =
    TyMap.iter (fun target envs ->
        ContextEnvs.iter (fun (env, _) ->
            let ty = env2fun arity env target in
            f ty env
          ) envs
      )

  let compare : t -> t -> int = TyMap.compare ContextEnvs.compare

  let equal (te1 : t) (te2 : t) : bool = TyMap.equal ContextEnvs.equal te1 te2

  let to_string (te : t) =
    Utilities.string_of_list Utilities.id @@
    List.map (fun (target, envs) ->
        string_of_ty target ^ " => " ^ ContextEnvs.to_string envs
      ) @@
    TyMap.bindings te
end

(** target -> environments *)
type te = TargetEnvs.t
