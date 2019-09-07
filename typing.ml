open Binding
open Context
open Environment
open GrammarCommon
open HGrammar
open HtyStore
open TargetEnvs
open Type
open TypingCommon
open Utilities

class typing (hg : hgrammar) = object(self)
  (* --- registers --- *)

  (** nt_ity[nt] has all typings of nonterminal nt. *)
  val nt_ity : ity array = Array.make hg#nt_count TyList.empty

  (** htys[id] contains list of types derived under some environment for
      corresponding terms in the list of terms identified by id. *)
  val hty_store : hty_store = new hty_store hg

  (* --- getting registered typings --- *)

  method nt_ty_exists (nt : nt_id) (ty : ty) : bool =
    TyList.exists (fun nt_ty -> nt_ty = ty) nt_ity.(nt)

  method nt_ity (nt : nt_id) : ity = nt_ity.(nt)

  (* --- saving new typings --- *)

  method add_nt_ity (nt : nt_id) (ity : ity) : bool =
    let new_ity_count = ref @@ TyList.length ity in
    nt_ity.(nt) <- TyList.merge_custom (fun x _ ->
        new_ity_count := !new_ity_count - 1;
        x
      ) nt_ity.(nt) ity;
    !new_ity_count <> 0

  method add_nt_ty (nt : nt_id) (ty : ty) : bool =
    self#add_nt_ity nt @@ TyList.singleton ty

  method add_hterms_hty (id : hterms_id) (hty : hty) : bool =
    hty_store#add_hty id hty

  (* --- generating envs --- *)

  (*
  (** Converts bindings in the form "hterms identified by id are substituted for arguments i-j"
      into bindings in the form "arguments i-j have the types <list of types>". If mask is
      not None then typings of all other variables will be replaced with T. If fixed_hterms_hty
      = Some (id, hty) then hty is used as a type of hterms identified with id in at least one
      occurence of id in the binding. *)
  method binding2hty_bindings (mask : vars option) (binding : hterms_id binding)
      (fixed_hterms_hty : (hterms_id * hty) option) : hty binding list =
    (* Ignoring the mask if it contains all variables. *)
    let mask = match mask with
      | None -> None
      | Some mask ->
        let mask_size = SortedVars.length mask in
        (* Mask may be ignored if it is equal to all variables. *)
        if mask_size = 0 || mask_size <> hg#nt_arity (fst @@ SortedVars.hd mask) then
          Some mask
        else
          None
    in
    (* Replaces hty on indexes not mentioned in vars by T. *)
    let apply_hty_mask mask i hty =
      let rec apply_hty_mask_aux mask index acc hty =
        match hty with
        | [] -> List.rev acc
        | ity :: hty' ->
          match SortedVars.hd_tl_option mask with
          | None ->
            apply_hty_mask_aux mask (index + 1) (ity_top :: acc) hty'
          | Some ((_, mask_index), mask') ->
            if mask_index = index then
              apply_hty_mask_aux mask' (index + 1) (ity :: acc) hty'
            else if mask_index < index then
              apply_hty_mask_aux mask' index acc hty
            else
              apply_hty_mask_aux mask (index + 1) (ity_top :: acc) hty'
      in
      apply_hty_mask_aux mask i [] hty
    in
    match binding, fixed_hterms_hty with
    | [], _ -> [[]]
    | _, Some (fixed_id, fixed_hty) ->
      (* Preparing types for the product and applying the mask if needed. Specifically,
         it contains the range of arguments i-j, possible hty without the fixed hty,
         masked fixed hty (if mask is defined) and information whether arguments i-j have id
         that can have fixed hty. *)
      let htys_raw_binding : (int * int * hty list * hty * bool) list =
        fold_left_short_circuit_after_first [] binding [] (fun acc (i, j, id) ->
            match hty_store#get_htys id with
            | [] -> []
            | htys ->
              match mask with
              | None ->
                (* Case without mask.
                   If there is a fixed_hty, it has to be filtered out. *)
                let htys = if id = fixed_id then
                    htys |> remove_first @@ hty_eq fixed_hty
                  else
                    htys
                in
                (i, j, htys, fixed_hty, id = fixed_id) :: acc
              | Some vars ->
                (* When two different hty have a mask applied, they may become the same hty
                   and can be merged, so duplicates have to be removed. *)
                (* TODO htys are being sorted here each time, so maybe keep them sorted.
                   or use a set. *)
                let masked_htys =
                  remove_hty_duplicates @@ List.rev_map (apply_hty_mask vars i) htys
                in
                (* The mask is applied to fixed_hty only when it is fixed_id, otherwise a dummy
                   value is used. *)
                let masked_fixed_hty =
                  if id = fixed_id then
                    apply_hty_mask vars i fixed_hty
                  else
                    []
                in
                (* If there is a fixed_hty, it has to filtered out after applying mask
                   because it will be present there in the product anyway and not removing it
                   would create duplicates. *)
                let masked_htys = if id = fixed_id then
                    masked_htys |> remove_first @@ hty_eq masked_fixed_hty
                  else
                    masked_htys
                in
                (i, j, masked_htys, masked_fixed_hty, id = fixed_id) :: acc
          )
      in
      (* Hterms with fixed_id are treated differently. *)
      let fixed_bindings, non_fixed_bindings =
        htys_raw_binding |> List.partition (fun (_, _, _, _, fixed) -> fixed)
      in
      (* Computing product with at least one fixed_hty placed instead of normal types of
         fixed_id. *)
      let fixed_bindings_product : hty binding list =
        product_with_one_fixed
          (fixed_bindings |> List.rev_map (fun (i, j, htys, _, _) ->
               htys |> List.rev_map (fun hty -> (i, j, hty))
             )
          )
          (fixed_bindings |> List.rev_map (fun (i, j, _, fixed_hty, _) -> (i, j, fixed_hty)))
      in
      (* Combining output of the product for fixed_id with types for the rest of the binding. *)
      flat_product @@ List.fold_left (fun acc (i, j, htys, _, _) ->
          List.rev_map (fun hty -> [(i, j, hty)]) htys :: acc
        ) [fixed_bindings_product] non_fixed_bindings
    | _, None ->
      (* Same as all of the above, but without the logic and additional computations for
         fixed_id. *)
      product @@ fold_left_short_circuit_after_first [] binding [] (fun acc (i, j, id) ->
          match hty_store#get_htys id with
          | [] -> []
          | htys ->
            let htys = match mask with
              | None -> htys
              | Some vars ->
                remove_hty_duplicates @@ List.rev_map (apply_hty_mask vars i) htys
            in
            List.rev_map (fun hty -> (i, j, hty)) htys :: acc
        )
                                                      
  (** Converts binding to possible environments using information on possible typings of hterms
      flowing into given variables without regard for the context in which they were typed.
      If mask is not None then only variables with specified indexes will be in the environment
      and other will have type T. This can reduce the cost of creating the environment, as
      replacing types with T can generate duplicates that are removed before computing a product.
      This does not return duplicate environments, as it is the product of unique typings taken
      from htys and hty_store does not store duplicates.
      If fixed_hterms_hty is not None, then bindings have at least one of hterms with given
      id typed as fixed hty. *)
  method binding2envs (var_count : int) (mask : vars option)
      (fixed_hterms_hty : (hterms_id * hty) option) (binding : hterms_id binding) : envs =
    Envs.of_list_empty_meta @@
    List.map (hty_binding2env var_count) @@
    self#binding2hty_bindings mask binding fixed_hterms_hty
  *)

  (** Constructs product environment for hterms in the binding and a map from variable positions
      (i.e., without nonterminal) to index of hterm in the product environment (ih). *)
  method binding2ctx (hterm : hterm) (mask : vars option)
      (fixed_hterms_hty : (hterms_id * hty) option)
      (fixed_nt_ty : (nt_id * ty) option)
      (binding : hterms_id binding) : ctx =
    let var_bix = var_bix binding in
    let bix_data = IntMap.of_list @@ index_list binding in
    let apply_mask =
      match mask with
      | None -> fun _ hty -> hty
      | Some mask ->
        let maskSet = IntSet.of_list @@ List.map snd @@ SortedVars.to_list mask in
        fun i hty ->
          List.map (fun (ix, ity) ->
              if IntSet.mem (ix + i) maskSet then
                ity
              else
                ity_top
            ) @@ index_list hty
    in
    let bix_htys =
      IntMap.map (fun (i, _, id) ->
          List.map (apply_mask i) @@
          hty_store#get_htys id
        ) bix_data
    in
    (* assuming that forced hty is present in bix_hty *)
    let forced_hterms_hty =
      match fixed_hterms_hty with
      | Some (fid, fhty) ->
        let bixs =
          List.map fst @@
          List.filter (fun (bix, (_, _, id)) ->
              id = fid
            ) @@
          IntMap.bindings bix_data
        in
        assert (List.for_all (fun bix ->
            List.exists (hty_eq fhty) @@ IntMap.find bix bix_htys
          ) bixs);
        Some (bixs, fhty)
      | None -> None
    in
    (* assuming that forced ty is in nt_ity *)
    let forced_nt_ty =
      match fixed_nt_ty with
      | Some (nt, ty) ->
        let locs =
          List.map fst @@
          List.filter (fun (l, (h, i)) -> h = HNT nt) @@
          HlocMap.bindings @@
          hg#loc2head_occurence hterm
        in
        assert (TyList.mem ty nt_ity.(nt));
        Some (locs, ty)
      | None -> None
    in
    mk_ctx var_bix bix_htys forced_hterms_hty nt_ity forced_nt_ty

  (* --- typing --- *)
  
  method terminal_ity : terminal -> ity =
    let a_ity = TyList.of_list [
        mk_fun [ity_np] true;
        mk_fun [ity_pr] true
      ]
    in
    let b_ity = TyList.of_list [
        mk_fun [ity_np; ity_top] false;
        mk_fun [ity_pr; ity_top] false;
        mk_fun [ity_top; ity_np] false;
        mk_fun [ity_top; ity_pr] false
      ]
    in
    let e_ity = ity_np in
    let t_ity = TyList.of_list [
        mk_fun [ity_np; ity_np] false;
        mk_fun [ity_pr; ity_np] false;
        mk_fun [ity_np; ity_pr] false;
        mk_fun [ity_pr; ity_pr] false
      ]
    in
    function
    | A -> a_ity
    | B -> b_ity
    | E -> e_ity
    | T -> t_ity

  (** Infer variable environments under which type checking of hterm : target succeeds. If target
      is not specified, environments are inferred for all possible targets. Returns the result
      in form of target -> possible environments map.
      The typing is done in a prefix order on the term tree. Types of terminals are constant,
      and types of nonterminals and variables are taken from the environment's context.
      The environment's context takes care of enforcing a usage of a specific typing of a
      nonterminal or a hterm. It is also used to keep possible variable typings as a product
      of variable typings as long as possible, since in many cases these typings will be invalid.
      Flag no_pr_vars prevents usage of productive variables. Flag force_pr_var ensures that
      there is at least one productive variable. Only one of these flags may be true.
      This method delegates the typing to type_check_hterm and later filters out results whose
      contexts did not satisfy restrictions that given typing of a nonterminal or hterms must
      be used at least once. It is necessary to do it here after traversing the whole term tree,
      because a nonterminal or hterms may simply never be typed if one of nodes above has
      type T. *)
  method type_check (hterm : hterm) (target : ty option) (ctx : ctx)
      (no_pr_vars : bool) (force_pr_var : bool) : te =
    let te = self#type_check_hterm hterm target ctx 0 no_pr_vars force_pr_var in
    print_verbose !Flags.verbose_proofs @@ lazy (
      "TE size before filtering out contexts that do not satisfy restrictions: " ^
      (string_of_int @@ TargetEnvs.size te) ^ "."
    );
    let res = te |> TargetEnvs.filter_satisfied_ctx in
    print_verbose !Flags.verbose_proofs @@ lazy (
      "TE size after filtering out contexts that do not satisfy restrictions: " ^
      (string_of_int @@ TargetEnvs.size res) ^ "."
    );
    res
        
  (** This method types leafs, i.e., terminals, nonterminals, and variables. Taking care of
      application is delegated to another method. *)
  method type_check_hterm (hterm : hterm) (target : ty option) (ctx : ctx) (loc : hloc)
      (no_pr_vars : bool) (force_pr_var : bool) : te =
    assert (not (no_pr_vars && force_pr_var));
    print_verbose !Flags.verbose_proofs @@ lazy (
      let vars_info = match no_pr_vars, force_pr_var with
        | true, false -> " (no pr vars)"
        | false, true -> " (force pr var)"
        | _ -> ""
      in
      let target_info =
        match target with
        | Some target -> " : " ^ string_of_ty target;
        | None -> ""
      in
      "Inferring environment for " ^ hg#string_of_hterm true HlocMap.empty 0 hterm ^
      target_info ^ vars_info
    );
    let res = match hterm with
      | HT a, [] ->
        if not force_pr_var then
          let ity = self#terminal_ity a in
          let filtered =
            match target with
            | Some target ->
              ity |> TyList.filter (Ty.equal target)
            | None -> ity
          in
          TargetEnvs.of_list @@
          TyList.map (fun ty -> (ty, [
              (mk_empty_env empty_used_nts (loc_with_single_type loc ty) (is_productive ty),
               ctx)
            ])) @@
          filtered
        else
          TargetEnvs.empty
      | HNT nt, [] ->
        if not force_pr_var then
          let compatible_ctx =
            match target with
            | Some target ->
              ctx_enforce_nt ctx loc target
            | None ->
              ctx_split_nt ctx nt loc
          in
          TargetEnvs.of_list @@
          List.map (fun (ty, ctx) -> (ty, [
              (mk_empty_env (nt_ty_used_once nt ty) (loc_with_single_type loc ty) false,
               ctx)
            ])) @@
          compatible_ctx
        else
          TargetEnvs.empty
      | HVar v, [] ->
        begin
          match target with
          | Some target ->
            if is_productive target then
              (* variables are only NP *)
              TargetEnvs.empty
            else
              begin
                let compatible_ctx =
                  if no_pr_vars then
                    ctx_enforce_var ctx v target
                  else if force_pr_var then
                    let pr_target = with_productivity true target in
                    ctx_enforce_var ctx v pr_target
                  else
                    (* both NP and PR versions are possible *)
                    let pr_target = with_productivity true target in
                    ctx_enforce_var ctx v target @ ctx_enforce_var ctx v pr_target
                in
                (* selecting a typing for a variable fixes hty to occurence of hterms, so
                   for each variable type a context where that variable has that type is used
                   effectively splitting the context into one piece per used variable type *)
                TargetEnvs.of_list @@
                List.map (fun (ty, ctx) ->
                    let env =
                      singleton_env empty_used_nts (loc_with_single_type loc ty) false v @@ sty ty
                    in
                    (target, [(env, ctx)])
                  ) @@
                compatible_ctx
              end
          | None ->
            (* if we're in this branch with None target then this must be a head variable or the
               whole term is a variable *)
            (* TODO maybe change definition of headvar to include var-only terms *)
            TargetEnvs.of_list @@
            List.map (fun (ty, ctx) ->
                let env =
                  singleton_env empty_used_nts (loc_with_single_type loc ty) false v @@ sty ty
                in
                (with_productivity false ty, [(env, ctx)])
              ) @@
            ctx_split_var ctx v
        end
      | _ -> (* application *)
        let h, args = hg#decompose_hterm hterm in
        self#type_check_app h args target ctx loc no_pr_vars force_pr_var
    in
    assert (target = None || TargetEnvs.targets_count res <= 1);
    print_verbose !Flags.verbose_proofs @@ lazy (
      let check_info =
        if TargetEnvs.is_empty res then
          " does not type check"
        else
          " type checks with the following targets and environments: " ^
          TargetEnvs.to_string res
      in
      hg#string_of_hterm true HlocMap.empty 0 hterm ^ check_info
    );
    res

  (** This method is used to type check an application of head h to arguments args. *)
  method type_check_app (h : head) (args : hterm list) (target : ty option) (ctx : ctx)
      (loc : hloc) (no_pr_vars : bool) (force_pr_var : bool) : te =
    (* Definitions:
       * target is the type used in type checking hterm h : target and is either restricted to
         type in argument or all possible targets are computed
       * target argument's productivity is the productivity of an argument in target type
       * actual argument's productivity is computed productivity of the type of an argument and
         it does not have to be the same as productivity of the target argument
       * head's type is the type of h, where h is a variable, terminal, or nonterminal *)
    let h_arity = List.length args in
    (* Get all head typings using type_check. Head typings are targets of this TE. Note that
       types of variables may have different productivity from the variable itself. *)
    let all_h_te = self#type_check_hterm (h, []) None ctx loc no_pr_vars force_pr_var in
    (* Filtering compatible head types so that the type after application will be equal to
       target type. *)
    let h_data =
      target |>
      option_map_or_default all_h_te @@
      self#filter_compatible_heads all_h_te h_arity
    in
    print_verbose !Flags.verbose_proofs @@ lazy (
      "head_ity: " ^
      string_of_ity (TyList.of_list @@ TargetEnvs.targets all_h_te) ^ "\n" ^
      "compatible head_ity: " ^
      string_of_ity (TyList.of_list @@ TargetEnvs.targets h_data)
    );
    (* Iteration over each compatible with the target typing of the head. annotate_args
       takes care of grouping types of arguments with their respective terms in args. h_target
       is the *)
    List.fold_left TargetEnvs.union TargetEnvs.empty @@
    (self#annotate_args args (loc + 1) h_data |>
     List.map (fun (args, h_target, env, ctx) ->
         (* Computing target for current typing of head and categorizing it by productivity. *)
         let head_pr = is_productive h_target in
         let pr_target, np_target = match target with
           | Some target ->
             (* When target is given, it is used. *)
             if is_productive target then
               (Some target, None)
             else
               (None, Some target)
           | None ->
             (* When target is not given, it is inferred from head's type. There is one
                possibility if head is productive and two if not. *)
             if head_pr then
               (Some h_target, None)
             else
               (Some (with_productivity true h_target), Some h_target)
         in
         (* Construction of a TE with starting variables for each target. *)
         let pr_start_te =
           pr_target |> option_map_or_default TargetEnvs.empty (fun target ->
               TargetEnvs.of_list [(target, [(env, ctx)])]
             )
         in
         let np_start_te =
           np_target |> option_map_or_default TargetEnvs.empty (fun target ->
               TargetEnvs.of_list [(target, [(env, ctx)])]
             )
         in
         let initial_te = TargetEnvs.union pr_start_te np_start_te in
         (* Delegating computation of TE with args of known types and known target to another
            method. *)
         self#type_check_targeted_app initial_te pr_target np_target args h_target env ctx
           no_pr_vars force_pr_var
       )
    )

  (** Assume that the target is
      /\_i t_1i -> .. -> /\_i t_ki -> t
      with t = pr or np. Typings of h that could make the application have the target type are
      * -> .. -> * -> /\_i t_1i -> .. -> /\_i t_ki -> *
      with some restrictions. If target = NP then t = np, but any * could be valid without
      additional information about duplication. If t = PR then t = pr or at least one of * is
      pr. *)
  method filter_compatible_heads (h_te : te) (arity : int) (target : ty) : te =
    let filter : ty -> bool =
      if is_productive target then
        let np_target = with_productivity false target in
        (fun ty ->
           let arg_itys, res_ty = split_ty ty arity in
           Ty.equal res_ty target ||
           Ty.equal res_ty np_target &&
           List.fold_left (fun acc ity ->
               TyList.fold_left (fun acc ty ->
                   if is_productive ty then
                     acc + 1
                   else
                     acc
                 ) acc ity
             ) 0 arg_itys >= 1
        )
      else
        (fun ty ->
           let res_ty = remove_args ty arity in
           Ty.equal res_ty target
        )
    in
    h_te |> TargetEnvs.filter_targets filter

  (** Annotates terms with their target types to split up the work easier. Preserves metadata. *)
  method annotate_args (terms : hterm list) (loc : hloc)
      (te : te) : ((hterm * (ity * hloc)) list * ty * env * ctx) list =
    let len = List.length terms in
    (* computing locations of leafs of arguments *)
    let arg_locs =
      List.rev @@ snd @@ List.fold_left (fun (arg_loc, arg_locs) arg_hterm ->
          let arg_hterm_size = hg#hterm_size arg_hterm in
          (arg_loc + arg_hterm_size, arg_loc :: arg_locs)
        ) (loc, []) terms
    in
    TargetEnvs.to_list te |>
    List.fold_left (fun acc (ty, envs) ->
        let arg_itys, codomain = split_ty ty len in
        List.fold_left (fun acc (env, ctx) ->
            (List.combine terms @@ List.combine arg_itys arg_locs, codomain, env, ctx) :: acc
          ) [] envs
      ) []

  (** Computation of TE of an application where target type and types of each argument are
      known. Targets differing only by productivity are grouped together because they have
      some common typings of whole subtrees in some situations. *)
  method type_check_targeted_app (initial_te : te) (pr_target : ty option) (np_target : ty option)
      (args : ((hterm * (ity * hloc)) list)) (h_target : ty)
      (env : env) (ctx : ctx) (no_pr_vars : bool) (force_pr_var : bool) : te =
    let head_pr = is_productive h_target in
    print_verbose !Flags.verbose_proofs @@ lazy (
      let head_info =
        if head_pr then
          " -> ... -> pr"
        else
          " -> ... -> np";
      in
      "* Type checking " ^
      String.concat " -> " (args |> List.map (fun (arg_term, (arg_ity, _)) ->
          "(" ^ hg#string_of_hterm true HlocMap.empty 0 arg_term ^ " : " ^
          string_of_ity arg_ity ^ ")"
        )) ^
      head_info
    );
    indent (+1);
    (* TODO update description *)
    (* The target is args = (arg_i: arg_ity_i)_i and the codomain is head_pr.
       Iterate over arguments while intersecting variable environments with short-circuit.
       Note that below productive argument describes productivity of the argument term, not
       productivity of the argument in head's type.

       When the target is productive, there are three options:
       (1) head is productive and there are no restrictions on arguments, or
       (2) head is not productive and at least one argument is productive, or
       (3) head is not productive and all arguments are not productive and there
         is a duplication (which implies that at least two arguments are
         productive in head type assuming no head variables).

       (NP) When the target is not productive, the head is not productive, no
          arguments are productive, and there are no duplications. There still can
          be productive arguments in head's type, as long as that does not force a
          duplication. *)
    (* TODO somehow include changing contexts. *)
    let te = fold_left_short_circuit initial_te args TargetEnvs.empty
        (fun te (arg_term, (arg_ity, arg_loc)) ->
           (* te contains not only variable environments, but also information whether
              there was a duplication (for (3) and (NP)) and whether a productive argument
              was used (for (3)). *)
           TyList.fold_left_short_circuit te arg_ity TargetEnvs.empty
             (fun te arg_ty ->
                print_verbose !Flags.verbose_proofs @@ lazy (
                  "* Typing argument " ^
                  hg#string_of_hterm true HlocMap.empty 0 arg_term ^ " : " ^
                  string_of_ity arg_ity
                );
                indent (+1);
                (* te are possible variable environments constructed so far from previous
                   arguments, only for the current target.
                   When target argument is productive, the actual argument can be either
                   productive or not productive, but with a productive variable. When
                   target argument is not productive, the actual argument must be not
                   productive and have no productive variables. *)
                let arg_te =
                  self#type_check_arg arg_term arg_ty pr_target np_target ctx arg_loc
                    no_pr_vars force_pr_var
                in
                let intersection = TargetEnvs.intersect te arg_te in
                print_verbose !Flags.verbose_proofs @@ lazy (
                  "retargeted envs for the argument: " ^
                  TargetEnvs.to_string arg_te ^ "\n" ^
                  "intersected with envs: " ^
                  TargetEnvs.to_string te ^ "\n" ^
                  "env count for the argument: " ^
                  string_of_int (TargetEnvs.size arg_te) ^ "\n" ^
                  "env count after intersection: " ^
                  string_of_int (TargetEnvs.size intersection)
                );
                (* Productive target might require duplication in (3), but this can only
                   be checked at the end. (or TODO optimization in argument order).
                   Nonproductive target requires no duplication. *)
                let res = TargetEnvs.filter_no_dup_for_np_targets intersection in
                print_verbose !Flags.verbose_proofs @@ lazy (
                  "env count after no duplication filtering: " ^
                  string_of_int (TargetEnvs.size res)
                );
                indent (-1);
                res
             )
        )
    in
    print_verbose !Flags.verbose_proofs @@ lazy (
      "* Intersected envs before duplication filtering:\n" ^
      "  " ^ TargetEnvs.to_string te
    );
    let te =
      if not head_pr then
        begin
          (* a duplication or productive actual argument is required when head is not
             productive and target is productive *)
          let te = TargetEnvs.filter_dup_or_pr_arg_for_pr_targets te in
          print_verbose !Flags.verbose_proofs @@ lazy (
            "* env count after duplication or pr arg filtering: " ^
            string_of_int (TargetEnvs.size te)
          );
          te
        end
      else
        te
    in
    if force_pr_var then
      let te = TargetEnvs.filter_pr_vars te in
      print_verbose !Flags.verbose_proofs @@ lazy (
        "* env count after pr var filtering: " ^
        string_of_int (TargetEnvs.size te)
      );
      indent (-1);
      te
    else
      begin
        indent (-1);
        te
      end

  (** Type checking argument of an application with known argument typing (but unknown actual
      typing) for up to two versions of a target at once with common context. *)
  method type_check_arg (hterm : hterm) (arg_target : ty)
      (pr_target : ty option) (np_target : ty option)
      (ctx : ctx) (loc : hloc)
      (no_pr_vars : bool) (force_pr_var : bool) : te =
    if is_productive arg_target then
      (* case when target argument is productive *)
      (* subcase when actual argument is productive *)
      let pr_arg_te =
        (* productive actual argument implies productive target *)
        match pr_target with (* TODO target is in keys of te *)
        | Some pr_target ->
          (* Retarget also marks these environments with information that
             productive actual argument was used and removes duplication
             flags. Not passing the force_pr_var flag, since this is one of
             many arguments. *)
          TargetEnvs.retarget pr_target @@
          self#type_check_hterm hterm (Some arg_target) ctx loc no_pr_vars false
        | None -> TargetEnvs.empty
      in
      (* subcase when actual argument is nonproductive *)
      let np_arg_te =
        if no_pr_vars then
          TargetEnvs.empty
        else
          (* productive target argument together with not productive actual
             argument implies productive variable *)
          let arg_te =
            self#type_check_hterm hterm (Some (with_productivity false arg_target))
              ctx loc false true
          in
          (* both target productivities are valid for nonproductive actual
             argument *)
          let pr_target_arg_te = match pr_target with
            | Some pr_target -> TargetEnvs.retarget pr_target arg_te
            | None -> TargetEnvs.empty
          in
          let np_target_arg_te = match np_target with
            | Some np_target -> TargetEnvs.retarget np_target arg_te
            | None -> TargetEnvs.empty
          in
          TargetEnvs.union pr_target_arg_te np_target_arg_te
      in
      TargetEnvs.union pr_arg_te np_arg_te
    else
      (* case when target argument is nonproductive *)
      (* nonproductive target argument implies nonproductive actual argument
         and no productive vars *)
      let arg_te =
        self#type_check_hterm hterm (Some arg_target) ctx loc true false
      in
      (* both target productivities are valid for nonproductive target
         argument *)
      let pr_target_arg_te = match pr_target with
        | Some pr_target -> TargetEnvs.retarget pr_target arg_te
        | None -> TargetEnvs.empty
      in
      let np_target_arg_te = match np_target with
        | Some np_target -> TargetEnvs.retarget np_target arg_te
        | None -> TargetEnvs.empty
      in
      TargetEnvs.union pr_target_arg_te np_target_arg_te

  (* --- printing --- *)

  method string_of_nt_ity : string =
    "Types of nonterminals:\n" ^
    String.concat "\n" @@ (range 0 hg#nt_count |> List.map (fun nt ->
        hg#nt_name nt ^ ": " ^ string_of_ity nt_ity.(nt)
      ))

  method string_of_hterms_hty (should_be_printed : hterms_id -> bool) : string =
    "Types of hterms:\n" ^
    String.concat "\n" @@ List.filter (fun s -> s <> "")
      (range 0 hg#hterms_count |> List.map (fun id ->
           if should_be_printed id then
             let htys = hty_store#get_htys id in
             string_of_int id ^ ":\n" ^
             concat_map "\n" (string_of_list string_of_ity) htys
           else
             ""
         ))

  (* --- debugging --- *)

  method get_hty_store = hty_store
end
