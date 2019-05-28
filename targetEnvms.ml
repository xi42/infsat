open GrammarCommon
open Environment
open HGrammar
open Type
open TypingCommon
open Utilities

(* TODO this doesn't work - it can be same hloc duplicated if in intersection type *)

(** Map from used nonterminal typings to where and how many times they were used in proof's
    hterm. *)
type used_nts = int HlocMap.t NTTyMap.t

let empty_used_nts : used_nts = NTTyMap.empty

let nt_ty_used_once (nt : nt_id) (ty : ty) (loc : hloc) : used_nts =
  NTTyMap.singleton (nt, ty) @@ HlocMap.singleton loc 1

(** Map from used terminal typings to where they were used in proof's hterm. *)
type used_ts = int HlocMap.t TTyMap.t

let empty_used_ts : used_ts = TTyMap.empty

let t_ty_used_once (a : terminal) (ty : ty) (loc : hloc) : used_ts =
  TTyMap.singleton (a, ty) @@ HlocMap.singleton loc 1

(** Environment with metadata - whether a duplication occured, whether a productive
    actual argument was used when computing given environment, which nonterminal and terminal
    types were used, if duplication occured anywhere in the whole proof subtree. *)
type envm = { env : env; dup : bool; pr_arg : bool; used_nts : used_nts; used_ts: used_ts;
              positive : bool }

let mk_envm_empty_flags (env : env) : envm =
  { env = env; dup = false; pr_arg = false; used_nts = NTTyMap.empty; used_ts = TTyMap.empty;
    positive = false }

let mk_envm (used_nts : used_nts) (used_ts : used_ts) (positive : bool) (env : env) : envm =
  { env = env; dup = false; pr_arg = false; used_nts = used_nts; used_ts = used_ts;
    positive = positive }

let with_dup (dup : bool) (envm : envm) : envm =
  { envm with dup = dup }

let with_positive (positive : bool) (envm : envm) : envm =
  { envm with positive = positive }

let with_used_nts (used_nts : used_nts) (envm : envm) : envm =
  { envm with used_nts = used_nts }

let string_of_envm (envm : envm) : string =
  let dup_info = if envm.dup then " DUP" else "" in
  let pr_arg_info = if envm.pr_arg then " PR_ARG" else "" in
  let nts_info =
    if NTTyMap.is_empty envm.used_nts then
      ""
    else
      " NTS " ^ (NTTyMap.bindings envm.used_nts |>
                 Utilities.string_of_list (fun (nt_ty, locs) ->
                     string_of_nt_ty nt_ty ^
                     Utilities.string_of_list HlocMap.string_of_int_binding @@
                     HlocMap.bindings locs
                   )
                )
  in
  let ts_info =
    if TTyMap.is_empty envm.used_ts then
      ""
    else
      " TS " ^ (TTyMap.bindings envm.used_ts |>
                 Utilities.string_of_list (fun (t_ty, locs) ->
                     string_of_t_ty t_ty ^ " " ^
                     Utilities.string_of_list HlocMap.string_of_int_binding @@
                     HlocMap.bindings locs
                   )
                )
  in
  let positive_info = if envm.positive then " POS" else "" in
  envm.env#to_string ^ dup_info ^ pr_arg_info ^ nts_info ^ ts_info ^ positive_info

(** A set of environments and information whether a duplication occured when computing
    them. In other words, list of possible typings of variables delimited by ANDs, treated as
    if there was OR as the delimiter. *)
module Envms = struct
  include Set.Make (struct
      type t = envm
      let compare envm1 envm2 =
        Utilities.compare_pair
          Pervasives.compare
          (Utilities.compare_pair env_compare @@
           NTTyMap.compare @@ HlocMap.multi_compare)
          ((envm1.dup, envm1.pr_arg, envm1.positive), (envm1.env, envm1.used_nts))
          ((envm2.dup, envm2.pr_arg, envm2.positive), (envm2.env, envm2.used_nts))
    end)
  (* TODO keeping info other than multi is good for presentation, but the proof is the same - drop
   duplicate proofs that differ only with used_ts or with amount of used_nts per nt *)
      
  (** Conversion of list of envs to an envms assuming default flags. *)
  let of_list_empty_flags (l : env list) : t =
    of_list @@ List.map mk_envm_empty_flags l

  (** Returns the same envms with flags set to default values. *)
  let with_empty_temp_flags (envms : t) : t =
    map (fun envm -> {
          envm with dup = false; pr_arg = false
        }) envms

  let to_string (envms : t) : string =
    concat_map " \\/ " string_of_envm @@ elements envms
end

type envms = Envms.t

(** A map from targets to environments under which they occur with duplication information. *)
module TargetEnvms = struct
  module M = Map.Make (struct
      type t = ty
      let compare = Ty.compare
    end)

  type t = envms M.t

  (** Empty TE. *)
  let empty : t = M.empty

  (** Singleton TE with mapping from target to envm *)
  let singleton_of_envm (target : ty) (envm : envm) =
    M.singleton target @@ Envms.singleton envm

  (** Singleton TE with mapping from target to env with no duplication *)
  let singleton (target : ty) (env : env) =
    singleton_of_envm target @@ mk_envm_empty_flags env

  let union : t -> t -> t =
    M.union (fun target envms1 envms2 ->
        Some (Envms.union envms1 envms2)
      )

  let of_list (l : (ty * envm list) list) : t =
    Seq.fold_left (fun acc (target, envms) ->
        M.update target (fun envms' ->
            match envms' with
            | Some envms' -> Some (Envms.union envms envms')
            | None -> Some envms
          ) acc
      ) empty @@
    Seq.map (fun (target, envms) ->
        (target, Envms.of_list envms)) @@
    List.to_seq l

  (** Conversion of list of pairs target-envms to respective TE assuming default flags. *)
  let of_list_empty_flags (l : (ty * env list) list) : t =
    of_list @@ (l |> List.map (fun (target, envms) ->
        (target, List.map mk_envm_empty_flags envms)))

  let to_list (te : t) : (ty * envm list) list =
    List.map (fun (target, envms) -> (target, Envms.elements envms)) @@ M.bindings te

  let mem (te : t) (target : ty) : bool =
    M.mem target te

  let is_empty : t -> bool = M.is_empty

  let size (te : t) : int =
    M.fold (fun _ envms acc -> acc + Envms.cardinal envms) te 0

  let for_all (f : ty -> envm -> bool) : t -> bool =
    M.for_all (fun target envms ->
        Envms.for_all (fun envm -> f target envm) envms
      )

  (** Removes targets with empty list of envms. *)
  let remove_empty_targets : t -> t =
    M.filter (fun target envms -> not @@ Envms.is_empty envms)

  (** Returns TE with flags of environments set to default values and removes duplicates. *)
  let with_empty_temp_flags : t -> t =
    M.map Envms.with_empty_temp_flags

  (** Changes target of the sole element of TE. Requires TE to have exactly one target.
      Also removes duplication flag and sets productive actual argument flag to whether previous
      target was productive. *)
  let retarget (target : ty) (te : t) : t =
    assert (M.cardinal te <= 1);
    M.of_seq @@
    Seq.map (fun (target', envms') ->
        let envms =
          envms' |> Envms.map (fun envm -> {
                (* note this does not touch used_nts and positive so that information is
                   carried over *)
                envm with dup = false; pr_arg = is_productive target'
              })
        in
        (target, envms)
      ) @@
    M.to_seq te

  (** Returns filtered TE with only the environments that have no duplication for nonproductive
      targets. *)
  let filter_no_dup_for_np_targets (te : t) : t =
    remove_empty_targets @@ M.mapi (fun target envms ->
        if is_productive target then
          envms
        else
          Envms.filter (fun envm -> not envm.dup) envms
      ) te

  (** Returns filtered TE with only the environments that have a duplication for productive
      targets. *)
  let filter_dup_or_pr_arg_for_pr_targets (te : t) : t =
    remove_empty_targets @@ M.mapi (fun target envms ->
        if is_productive target then
          Envms.filter (fun envm -> envm.dup || envm.pr_arg) envms
        else
          envms
      ) te

  (** Returns filtered TE with only the environments that contain productive_vars. *)
  let filter_pr_vars (te : t) : t =
    remove_empty_targets @@ M.mapi (fun target envms ->
        Envms.filter (fun envm -> envm.env#has_pr_vars) envms
      ) te

  (** Flatten an intersection of variable environments, intersected separately for each target.
      Environments are essentially OR-separated sets of AND-separated sets of typings of
      variables. Flattening means moving outer intersection (AND) inside. *)
  let intersect : t -> t -> t =
    (* separately for each target *)
    M.merge (fun target envms1 envms2 ->
        match envms1, envms2 with
        | Some envms1, Some envms2 ->
          Some (
            (* for each envm in envms in te1 *)
            Envms.fold (fun envm1 acc ->
                (* for each envm in envms in te2 *)
                Envms.fold (fun envm2 acc ->
                    (* Merge them together, compute duplication, and reshape the list result into
                       a TE. This is the only place where duplication flag is set. If there was a
                       duplication, positive flag is updated to true too. *)
                    let env, merged_dup = envm1.env#merge envm2.env in
                    let merged_envm = {
                      env = env;
                      dup = envm1.dup || envm2.dup || merged_dup;
                      pr_arg = envm1.pr_arg || envm2.pr_arg;
                      used_nts =
                        NTTyMap.union (fun _ locs1 locs2 -> Some (HlocMap.sum_union locs1 locs2))
                          envm1.used_nts envm2.used_nts;
                      used_ts =
                        TTyMap.union (fun _ locs1 locs2 -> Some (HlocMap.sum_union locs1 locs2))
                          envm1.used_ts envm2.used_ts;
                      positive = envm1.positive || envm2.positive || merged_dup
                    }
                    in
                    Envms.add merged_envm acc
                  ) envms2 acc
              ) envms1 Envms.empty
          )
        | _, _ -> None
      )

  (** Returns the types of arguments to which terms typed as targets can be applied in
      variable environments of the target. *)
  let targets_as_args (te : t) : ity =
    TyList.remove_duplicates @@ TyList.of_list @@
    M.fold (fun target envms acc ->
        if is_productive target then
          target :: acc
        else
          (* assuming all listed targets have environments *)
          let some_envm = Envms.choose envms in
          if some_envm.env#has_pr_vars then
            if Envms.for_all (fun envm -> envm.env#has_pr_vars) envms then
              with_productivity true target :: acc
            else
              with_productivity true target :: target :: acc
          else if Envms.exists (fun envm -> envm.env#has_pr_vars) envms then
            with_productivity true target :: target :: acc
          else
            target :: acc
      ) te []

  let targets_count : t -> int = M.cardinal

  (** Creates function types from targets and variables in their environments and iterates over
      all resulting function types along with environment. *)
  let iter_fun_ty (f : ty -> envm -> unit) : t -> unit =
    M.iter (fun target envms ->
        Envms.iter (fun envm ->
            let ty = envm.env#mk_fun target in
            f ty envm
          ) envms
      )

  let compare : t -> t -> int = M.compare Envms.compare

  let equal (te1 : t) (te2 : t) : bool = compare te1 te2 = 0

  let to_string (te : t) =
    Utilities.string_of_list Utilities.id @@
    List.map (fun (target, envms) ->
        string_of_ty target ^ " => " ^ Envms.to_string envms
      ) @@
    M.bindings te
end

(** target -> environments *)
type te = TargetEnvms.t
