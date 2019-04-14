open GrammarCommon
open Environment
open Type
open Utilities

type nt_ty = nt_id * ty

let nt_ty_compare = Utilities.compare_pair Pervasives.compare Ty.compare

(** Map from used nonterminal typings to whether they were used twice or more. *)
module NTTyMap = Map.Make (struct
    type t = nt_id * ty
    let compare = nt_ty_compare
  end)

type used_nts = bool NTTyMap.t

let empty_used_nts : used_nts = NTTyMap.empty

let nt_ty_used_once (nt : nt_id) (ty : ty) : used_nts =
  NTTyMap.singleton (nt, ty) false

(** Environment with metadata - whether a duplication occured and whether a productive
    actual argument was used when computing a given environment. *)
type envm = { env : env; dup : bool; pr_arg : bool; used_nts : used_nts; positive : bool }

let mk_envm_empty_flags (env : env) : envm =
  { env = env; dup = false; pr_arg = false; used_nts = NTTyMap.empty; positive = false }

let mk_envm (used_nts : used_nts) (positive : bool) (env : env) : envm =
  { env = env; dup = false; pr_arg = false; used_nts = used_nts; positive = positive }

let with_used_nts (envm : envm) (used_nts : used_nts) : envm =
  { envm with used_nts = used_nts }

let string_of_envm (envm : envm) : string =
  let dup_info = if envm.dup then " DUP" else "" in
  let pr_arg_info = if envm.pr_arg then " PR_ARG" else "" in
  let nts_info =
    if NTTyMap.is_empty envm.used_nts then
      ""
    else
      " NTS " ^ (NTTyMap.bindings envm.used_nts |>
                 Utilities.string_of_list (fun ((nt, ty), multi) ->
                     let multi_info =
                       if multi then
                         " (multiple)"
                       else
                         ""
                     in
                     string_of_int nt ^ " : " ^ string_of_ty ty ^ multi_info
                   )
                )
  in
  let positive_info = if envm.positive then " POS" else "" in
  envm.env#to_string ^ dup_info ^ pr_arg_info ^ nts_info ^ positive_info

(** A set of environments and information whether a duplication occured when computing
    them. In other words, list of possible typings of variables delimited by ANDs, treated as
    if there was OR as the delimiter. *)
module Envms = struct
  include Set.Make (struct
      type t = envm
      let compare envm1 envm2 =
        Utilities.compare_pair
          Pervasives.compare
          (Utilities.compare_pair env_compare @@ NTTyMap.compare Pervasives.compare)
          ((envm1.dup, envm1.pr_arg, envm1.positive), (envm1.env, envm1.used_nts))
          ((envm2.dup, envm2.pr_arg, envm2.positive), (envm2.env, envm2.used_nts))
    end)

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

  (** Empty TEL. *)
  let empty : t = M.empty

  (** Singleton TEL with mapping from target to envm *)
  let singleton_of_envm (target : ty) (envm : envm) =
    M.singleton target @@ Envms.singleton envm

  (** Singleton TEL with mapping from target to env with no duplication *)
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

  (** Conversion of list of pairs target-envms to respective tel assuming default flags. *)
  let of_list_empty_flags (l : (ty * env list) list) : t =
    of_list @@ (l |> List.map (fun (target, envms) ->
        (target, List.map mk_envm_empty_flags envms)))

  let to_list (tel : t) : (ty * envm list) list =
    List.map (fun (target, envms) -> (target, Envms.elements envms)) @@ M.bindings tel

  let mem (tel : t) (target : ty) : bool =
    M.mem target tel

  let is_empty : t -> bool = M.is_empty

  let size (tel : t) : int =
    M.fold (fun _ envms acc -> acc + Envms.cardinal envms) tel 0

  let for_all (f : ty -> envm -> bool) : t -> bool =
    M.for_all (fun target envms ->
        Envms.for_all (fun envm -> f target envm) envms
      )

  (** Removes targets with empty list of envms. *)
  let remove_empty_targets : t -> t =
    M.filter (fun target envms -> not @@ Envms.is_empty envms)

  (** Returns TEL with flags of environments set to default values and removes duplicates. *)
  let with_empty_temp_flags : t -> t =
    M.map Envms.with_empty_temp_flags

  (** Changes target of the sole element of TEL. Requires TEL to have exactly one target.
      Also removes duplication flag and sets productive actual argument flag to whether previous
      target was productive. *)
  let retarget (target : ty) (tel : t) : t =
    assert (M.cardinal tel <= 1);
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
    M.to_seq tel

  (** Returns filtered TEL with only the environments that have no duplication for nonproductive
      targets. *)
  let filter_no_dup_for_np_targets (tel : t) : t =
    remove_empty_targets @@ M.mapi (fun target envms ->
        if is_productive target then
          envms
        else
          Envms.filter (fun envm -> not envm.dup) envms
      ) tel

  (** Returns filtered TEL with only the environments that have a duplication for productive
      targets. *)
  let filter_dup_or_pr_arg_for_pr_targets (tel : t) : t =
    remove_empty_targets @@ M.mapi (fun target envms ->
        if is_productive target then
          Envms.filter (fun envm -> envm.dup || envm.pr_arg) envms
        else
          envms
      ) tel

  (** Returns filtered TEL with only the environments that contain productive_vars. *)
  let filter_pr_vars (tel : t) : t =
    remove_empty_targets @@ M.mapi (fun target envms ->
        Envms.filter (fun envm -> envm.env#has_pr_vars) envms
      ) tel

  (** Flatten an intersection of variable environments, intersected separately for each target.
      Environments are essentially OR-separated sets of AND-separated sets of typings of
      variables. Flattening means moving outer intersection (AND) inside. *)
  let intersect : t -> t -> t =
    (* separately for each target *)
    M.merge (fun target envms1 envms2 ->
        match envms1, envms2 with
        | Some envms1, Some envms2 ->
          Some (
            (* for each envm in envms in tel1 *)
            Envms.fold (fun envm1 acc ->
                (* for each envm in envms in tel2 *)
                Envms.fold (fun envm2 acc ->
                    (* Merge them together, compute duplication, and reshape the list result into
                       a TEL. This is the only place where duplication flag is set. If there was a
                       duplication, positive flag is updated to true too. *)
                    let env, merged_dup = envm1.env#merge envm2.env in
                    let merged_envm = {
                      env = env;
                      dup = envm1.dup || envm2.dup || merged_dup;
                      pr_arg = envm1.pr_arg || envm2.pr_arg;
                      used_nts =
                        NTTyMap.union (fun _ _ _ -> Some true) envm1.used_nts envm2.used_nts;
                      positive = envm1.positive || envm2.positive || merged_dup
                    }
                    in
                    Envms.add merged_envm acc
                  ) envms2 acc
              ) envms1 Envms.empty
          )
        | _, _ -> None
      )
(*
  let map (f : ty -> envms -> 'a) (tel : t) : 'a list =
    TargetEnvmsListBase.map (fun (target, envms) -> f target envms) tel
*)

  (** Returns the types of arguments to which terms typed as targets can be applied in
      variable environments of the target. *)
  let targets_as_args (tel : t) : ity =
    TyList.remove_duplicates @@ TyList.of_list @@
    M.fold (fun target envms acc ->
        if is_productive target then
          target :: acc
        else
          (* assuming all listed targets have environments *)
          let some_envm = Envms.choose envms in
          if some_envm.env#has_pr_vars then
            if Envms.for_all (fun envm -> envm.env#has_pr_vars) envms then
              with_productivity PR target :: acc
            else
              with_productivity PR target :: target :: acc
          else if Envms.exists (fun envm -> envm.env#has_pr_vars) envms then
            with_productivity PR target :: target :: acc
          else
            target :: acc
      ) tel []

  let targets_count : t -> int = M.cardinal

  (** Creates function types from targets and variables in their environments and iterates over
      all resulting function types along with nonterminal typings used to create them and
      boolean whether duplication factor increased while computing them. *)
  let iter_fun_ty (f : ty -> used_nts -> bool -> unit) : t -> unit =
    M.iter (fun target envms ->
        Envms.iter (fun envm ->
            let ty = envm.env#mk_fun target in
            f ty envm.used_nts envm.positive
          ) envms
      )

  let compare : t -> t -> int = M.compare Envms.compare

  let equal (tel1 : t) (tel2 : t) : bool = compare tel1 tel2 = 0

  let to_string (tel : t) =
    Utilities.string_of_list Utilities.id @@
    List.map (fun (target, envms) ->
        string_of_ty target ^ " => " ^ Envms.to_string envms
      ) @@
    M.bindings tel
end

(** target -> environments *)
type tel = TargetEnvms.t
