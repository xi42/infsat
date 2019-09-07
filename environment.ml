open Binding
open GrammarCommon
open HGrammar
open TypingCommon
open Type
open Utilities

(** Map from used nonterminal typings to whether they were used at least twice in the proof
    tree. *)
type used_nts = bool NTTyMap.t

let empty_used_nts : used_nts = NTTyMap.empty

let nt_ty_used_once (nt : nt_id) (ty : ty) : used_nts =
  NTTyMap.singleton (nt, ty) false

(** Map from used terminal typings to where they were used in proof's hterm. *)
type loc_types = int TyMap.t HlocMap.t

let empty_loc_types : loc_types = HlocMap.empty

let loc_with_single_type (loc : hloc) (ty : ty) : loc_types =
  HlocMap.singleton loc @@ TyMap.singleton ty 1

(** Immutable typing environment for a term. Contains info on types of variables and various
    metadata gathered from the derivation tree for that term. *)
type env = {
  (** Mapping from variables to their intersection types. Logically, everything is connected with
      AND. *)
  vars : ity IntMap.t;
  (** Information if duplication occured when computing this environment on the top of the
      derivation tree. *)
  dup : bool;
  (** Information if productive actual argument was used on the top of the derivation tree. *)
  pr_arg : bool;
  (** Nonterminals used when computing this environment in the whole derivation tree.
      This is redundant due to loc_types, but allows for quick search of relevant
      for duplication graph info. loc_types is only used for pretty-printing proofs. *)
  used_nts : used_nts;
  (** Typings of terminals and nonterminals used in the derivation in different locations. *)
  loc_types : loc_types;
  (** Information if duplication or terminal a occured in the whole derivation tree. *)
  positive : bool
}

(* --- construction --- *)

let mk_env (used_nts : used_nts) (loc_types : loc_types) (positive : bool)
    (vars : ity IntMap.t) : env =
  {
    vars = vars;
    dup = false;
    pr_arg = false;
    used_nts = used_nts;
    loc_types = loc_types;
    positive = positive
  }

(** Make empty environment with given metadata, but with no duplications. *)
let mk_empty_env (used_nts : used_nts) (loc_types : loc_types) (positive : bool) : env =
  mk_env used_nts loc_types positive IntMap.empty
    
(** Creates an environment with empty metadata. Careful with making sure that location types are
    eventually added. *)
let mk_env_empty_meta (vars : ity IntMap.t) =
  mk_env empty_used_nts empty_loc_types false vars

let singleton_env (used_nts : used_nts) (loc_types : loc_types) (positive : bool)
    (_, i : var_id) (ity : ity) : env =
  mk_env used_nts loc_types positive @@ IntMap.singleton i ity

(* --- access --- *)

(*
  method var_count : int = Array.length var_itys

  method get_var_itys : ity array = var_itys

  method get_var_ity (_, i : var_id) : ity = var_itys.(i)

  method mk_fun (codomain : ty) : ty =
    cons_fun (Array.to_list var_itys) codomain

  method mem (v : var_id) (ty : ty) : bool =
    TyList.mem ty @@ self#get_var_ity v

  method has_pr_vars : bool =
    Array.exists (fun ity -> TyList.exists is_productive ity) var_itys
*)

let env2fun (env : env) (codomain : ty) : ty =
  cons_fun (List.map snd @@ IntMap.bindings env.vars) codomain

let env_has_pr_vars (env : env) : bool =
  IntMap.exists (fun _ ity -> TyList.exists is_productive ity) env.vars

(* --- transformation --- *)

let with_dup (dup : bool) (env : env) : env =
  { env with dup = dup }

let with_positive (positive : bool) (env : env) : env =
  { env with positive = positive }

let with_used_nts (used_nts : used_nts) (env : env) : env =
  { env with used_nts = used_nts }

let with_single_loc_ty (loc : hloc) (ty : ty) (env : env) : env =
  { env with loc_types = loc_with_single_type loc ty }

(** Merging vars is summation of itys of the same var. The result is a new, merged
    environment and information whether duplication of a productive variable occured. *)
let intersect_vars (vars1 : ity IntMap.t) (vars2 : ity IntMap.t) : ity IntMap.t * bool =
  let dup = ref false in
  let vars = IntMap.union (fun _ ity1 ity2 ->
      Some (TyList.merge_custom (fun ty _ ->
          if is_productive ty then
            dup := true;
          ty) ity1 ity2)
    ) vars1 vars2
  in
  vars, !dup

(** Merges two environments together, setting the duplication and positive flag if needed. *)
let intersect_envs (env1 : env) (env2 : env) =
  let vars, merged_dup = intersect_vars env1.vars env2.vars in
  {
    vars = vars;
    dup = env1.dup || env2.dup || merged_dup;
    pr_arg = env1.pr_arg || env2.pr_arg;
    used_nts =
      NTTyMap.union (fun _ _ _ -> Some true)
        env1.used_nts env2.used_nts;
    loc_types =
      HlocMap.union (fun _ ty_counts1 ty_counts2 ->
          Some (TyMap.union (fun _ count1 count2 ->
              Some (count1 + count2)
            ) ty_counts1 ty_counts2)
        ) env1.loc_types env2.loc_types;
    positive = env1.positive || env2.positive || merged_dup
  }

(* --- comparison --- *)

(** Compares two environments with the same amount of variables. Ignores loc_types, which means
    that locations and terminals are ignored and all used nonterminals in counts above 2 are
    treated as if the count was 2. *)
let env_compare (env1 : env) (env2 : env) : int =
  compare_pair
    compare
    (compare_pair (IntMap.compare TyList.compare) @@
     NTTyMap.compare compare)
    ((env1.dup, env1.pr_arg, env1.positive), (env1.vars, env1.used_nts))
    ((env2.dup, env2.pr_arg, env2.positive), (env2.vars, env2.used_nts))

let env_eq (env1 : env) (env2 : env) =
  env_compare env1 env2 = 0

(*
let env_hash (env : env) : int =
  Array.fold_left (fun acc x ->
      Hashtbl.hash (acc, Hashtbl.hash @@ List.map Ty.id_of_ty @@ TyList.to_list x)
    ) 0 env.vars
*)

(* --- printing --- *)

let string_of_env (env : env) : string =
  let vars_str =
    if IntMap.is_empty env.vars then
      "*"
    else
      String.concat ", " @@ List.of_seq @@
      Seq.map (fun (i, ity) -> string_of_int i ^ " : " ^ string_of_ity ity) @@
      IntMap.to_seq env.vars
  in
  let dup_info = if env.dup then " DUP" else "" in
  let pr_arg_info = if env.pr_arg then " PR_ARG" else "" in
  let nts_info =
    if NTTyMap.is_empty env.used_nts then
      ""
    else
      " NTS " ^ (NTTyMap.bindings env.used_nts |>
                 Utilities.string_of_list (fun (nt_ty, multi) ->
                     let multi_str =
                       if multi then
                         "+"
                       else
                         ""
                     in
                     string_of_nt_ty nt_ty ^ multi_str
                   )
                )
  in
  let loc_types_str =
    " LOC " ^ (HlocMap.bindings env.loc_types |>
               Utilities.string_of_list (fun (loc, ty_counts) ->
                   string_of_int loc ^ ": " ^
                   Utilities.string_of_list (fun (ty, count) ->
                       string_of_ty ty ^ " x" ^ string_of_int count
                     ) (TyMap.bindings ty_counts)
                 )
              )
  in
  let positive_info = if env.positive then " POS" else "" in
  vars_str ^ dup_info ^ pr_arg_info ^ nts_info ^ loc_types_str ^ positive_info
