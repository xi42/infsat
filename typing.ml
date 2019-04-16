open Binding
open Environment
open GrammarCommon
open HGrammar
open HtyStore
open TargetEnvms
open Type
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
                    remove_first htys @@ hty_eq fixed_hty
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
                    remove_first masked_htys @@ hty_eq masked_fixed_hty
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
  method binding2envms (var_count : int) (mask : vars option)
      (fixed_hterms_hty : (hterms_id * hty) option) (binding : hterms_id binding) : envms =
    Envms.of_list_empty_flags @@
    List.map (hty_binding2env var_count) @@
    self#binding2hty_bindings mask binding fixed_hterms_hty

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

  method private var_count : (env, int) either -> int = function
    | Left env -> env#var_count
    | Right var_count -> var_count

  (** Returns sorted list of typings available for given head term. *)
  method infer_head_ity (h : head) (env_data : (env, int) either) : (ty * envm) list =
    match h with
    | HNT nt ->
      let empty = mk_envm_empty_flags @@ empty_env @@ self#var_count env_data in
      nt_ity.(nt) |> TyList.map (fun ty ->
          (ty, empty |> with_used_nts @@ nt_ty_used_once nt ty)
        )
    | HVar v ->
      begin
        match env_data with
        | Left env ->
          env#get_var_ity v |> TyList.map (fun ty ->
              (with_productivity false ty,
               mk_envm_empty_flags @@ singleton_env (self#var_count env_data) v @@ sty ty)
            )
        | Right _ -> failwith "Expected environment provided for a term with head variables"
      end
    | HT a ->
      let empty = empty_env @@ self#var_count env_data in
      self#terminal_ity a |> TyList.map (fun ty -> (ty,
          mk_envm empty_used_nts (is_productive ty) empty
        ))

  (** Assume that the target is
      /\_i t_1i -> .. -> /\_i t_ki -> t
      with t = pr or np. Typings of h that could make the application have the target type are
      * -> .. -> * -> /\_i t_1i -> .. -> /\_i t_ki -> *
      with some restrictions. If target = NP then t = np, but any * could be valid without
      additional information about duplication. If t = PR then t = pr or at least one of * is
      pr. *)
  method filter_compatible_heads (ity_data : (ty * 'a) list) (arity : int)
      (target : ty) : (ty * 'a) list =
    if is_productive target then
      let np_target = with_productivity false target in
      ity_data |> List.filter (fun (ty, _) ->
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
      ity_data |> List.filter (fun (ty, _) ->
          let res_ty = remove_args ty arity in
          Ty.equal res_ty target
        )

  (** Creates a list of pairs (term, ity) with ity being intersection type for given
      argument, and each element of outer list corresponds to one of provided types.
      Combines that in a tuple with the rest of the type, metadata, and a boolean whether
      the whole type is productive. *)
  method annotate_args : 'a 'b. 'a list -> (ty * 'b) list ->
    (('a * ity) list * ty * 'b) list =
    fun terms ->
    let len = List.length terms in
    List.map (fun (ty, x) ->
        let args, codomain = split_ty ty len in
        (List.combine terms args, codomain, x)
      )
        
  (** Infer variable environments under which type checking of hterm : target succeeds. If target
      is not specified, environments are inferred for all possible targets. Types of variables
      are looked up in the supplied in env_data environment or inferred if only the number of
      variables is provided in env_data. Inference of variable types requires no head variables
      present in hterm.
      Flag no_pr_vars prevents inference of productive variables. Flag force_pr_var ensures that
      there is at least one productive variable. Only one of these flags may be true. *)
  method type_check (hterm : hterm) (target : ty option) (env_data : (env, int) either)
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
      "Inferring environment for " ^ hg#string_of_hterm hterm ^ target_info ^ vars_info ^ "\n"
    );
    let var_count = match env_data with
      | Left env -> env#var_count
      | Right var_count -> var_count
    in
    (* It is not possible to force a productive variable when there are no variables.
       If a target is given, checking if there is a terminal with maching types. *)
    let filter_ity_list ity mod_env =
      if not force_pr_var then
        let filtered =
          match target with
          | Some target ->
            ity |> TyList.filter (Ty.equal target)
          | None -> ity
        in
        TargetEnvms.of_list @@
        TyList.map (fun ty -> (ty, [mod_env ty @@ mk_envm_empty_flags @@ empty_env var_count])) @@
        filtered
      else
        TargetEnvms.empty
    in
    let res = match hterm with
      | HT a, [] ->
        filter_ity_list (self#terminal_ity a) (fun ty envm ->
            envm |> with_positive @@ is_productive ty
          )
      | HNT nt, [] ->
        filter_ity_list (self#nt_ity nt) (fun ty envm ->
            envm |> with_used_nts @@ nt_ty_used_once nt ty)
      | HVar v, [] ->
        begin
          match target, env_data with
          | Some target, _ ->
            (* if target is known then either the type is inferred from it or correct environment
               is just type checked *)
            let env_if_var_ty_available v ty =
              let available = match env_data with
                | Left env -> env#mem v ty
                | Right _ -> true
              in
              if available then
                TargetEnvms.singleton target @@ singleton_env var_count v @@ sty ty
              else
                TargetEnvms.empty
            in
            if is_productive target then
              TargetEnvms.empty (* variables are only NP *)
            else if no_pr_vars then
              env_if_var_ty_available v target
            else if force_pr_var then
              let pr_target = with_productivity true target in
              env_if_var_ty_available v pr_target
            else
              (* both NP and PR versions are possible *)
              let pr_target = with_productivity true target in
              TargetEnvms.union
                (env_if_var_ty_available v target) (env_if_var_ty_available v pr_target)
          | None, Left env ->
            (* if we're in this branch with None target then this must be a head variable or the
               whole term is a variable *)
            (* TODO maybe change definition of headvar to include var-only terms *)
            TargetEnvms.of_list_empty_flags @@
            TyList.map (fun ty ->
                (with_productivity false ty, [singleton_env var_count v @@ sty ty])
              ) @@
            env#get_var_ity v
          | None, Right _ -> failwith @@ "Type checking of terms with head variables or " ^
                                         "variable-only terms needs an environment"
        end
      | _ -> (* application *)
        let h, args = hg#decompose_hterm hterm in
        self#type_check_app h args target env_data no_pr_vars force_pr_var
    in
    assert (target = None || TargetEnvms.targets_count res <= 1);
    print_verbose !Flags.verbose_proofs @@ lazy (
      let check_info =
        if TargetEnvms.is_empty res then
          " does not type check"
        else
          " type checks with the following targets and environments: " ^
          TargetEnvms.to_string res
      in
      hg#string_of_hterm hterm ^ check_info ^ "\n"
    );
    res

  method type_check_app (h : head) (args : hterm list) (target : ty option)
      (env_data : (env, int) either) (no_pr_vars : bool) (force_pr_var : bool) : te =
    (* Definitions:
       * target is the type used in type checking hterm h : target and is either restricted to
         type in argument or all possible targets are computed
       * target argument's productivity is the productivity of an argument in target type
       * actual argument's productivity is computed productivity of the type of an argument and
         it does not have to be the same as productivity of the target argument
       * head's type is the type of h, where h is a variable, terminal, or nonterminal *)
    let h_arity = List.length args in
    (* Get all h typings *)
    let all_h_data = self#infer_head_ity h env_data in
    (* TODO var in head does not get into the env *)
    (* filtering compatible head types assuming head is not a variable *)
    let h_data = target |> option_map all_h_data
                  (self#filter_compatible_heads all_h_data h_arity)
    in
    print_verbose !Flags.verbose_proofs @@ lazy (
      "head_ity: " ^
      string_of_ity (TyList.of_list (List.map fst all_h_data)) ^ "\n" ^
      "compatible head_ity: " ^
      string_of_ity (TyList.of_list (List.map fst h_data)) ^ "\n"
    );
      (* TODO optimizations:
       * caching argument index * argument required productivity -> envms
       * computing terms without variables first and short circuit after for all terms
       * computing terms with non-duplicating variables last with short-circuiting when
         duplication is expected
       * pre-computing order of computing argument types
       * maybe cache with versioning or just cache of all typings
       * flag to choose optimization in order to benchmark them later *)
    (* Iteration over each possible typing of the head *)
    List.fold_left TargetEnvms.union TargetEnvms.empty @@
    (self#annotate_args args h_data |> List.map (fun (args, h_target, envm) ->
         (* computing targets *)
         let head_pr = is_productive h_target in
         let pr_target, np_target = match target with
           | Some target ->
             if is_productive target then
               (Some target, None)
             else
               (None, Some target)
           | None ->
             if head_pr then
               (Some h_target, None)
             else
               (Some (with_productivity true h_target), Some h_target)
         in
         (* construction of a TE with starting variables for each target (i.e., the variable from
            head if there is one) *)
         let pr_start_te =
           pr_target |> option_map TargetEnvms.empty (fun target ->
               TargetEnvms.singleton_of_envm target envm
             )
         in
         let np_start_te =
           np_target |> option_map TargetEnvms.empty (fun target ->
               TargetEnvms.singleton_of_envm target envm
             )
         in
         let start_te = TargetEnvms.union pr_start_te np_start_te in
         print_verbose !Flags.verbose_proofs @@ lazy (
           let head_info =
             if head_pr then
               " -> ... -> pr\n"
             else
               " -> ... -> np\n";
           in
           "* Type checking " ^
           String.concat " -> " (args |> List.map (fun (arg_term, arg_ity) ->
               "(" ^ hg#string_of_hterm arg_term ^ " : " ^ string_of_ity arg_ity ^ ")"
             )) ^
           head_info
         );
         indent (+1);
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
         let te = fold_left_short_circuit start_te args TargetEnvms.empty
             (fun te (arg_term, arg_ity) ->
                (* te contains not only variable environments, but also information whether
                   there was a duplication (for (3) and (NP)) and whether a productive argument
                   was used (for (3)). *)
                TyList.fold_left_short_circuit te arg_ity TargetEnvms.empty
                  (fun te arg_ty ->
                     print_verbose !Flags.verbose_proofs @@ lazy (
                       "* Typing argument " ^
                       hg#string_of_hterm arg_term ^ " : " ^
                       string_of_ity arg_ity ^ "\n"
                     );
                     indent (+1);
                     (* te are possible variable environments constructed so far from previous
                        arguments, only for the current target.
                        When target argument is productive, the actual argument can be either
                        productive or not productive, but with a productive variable. When
                        target argument is not productive, the actual argument must be not
                        productive and have no productive variables. *)
                     let arg_te =
                       if is_productive arg_ty then
                         (* case when target argument is productive *)
                         (* subcase when actual argument is productive *)
                         let pr_arg_te =
                           (* productive actual argument implies productive target *)
                           match pr_target with
                           | Some pr_target ->
                             (* Retarget also marks these environments with information that
                                productive actual argument was used and removes duplication
                                flags. Not passing the force_pr_var flag, since this is one of
                                many arguments. *)
                             TargetEnvms.retarget pr_target @@
                             self#type_check arg_term (Some arg_ty) env_data no_pr_vars false
                           | None -> TargetEnvms.empty
                         in
                         (* subcase when actual argument is nonproductive *)
                         let np_arg_te =
                           if no_pr_vars then
                             TargetEnvms.empty
                           else
                             (* productive target argument together with not productive actual
                                argument implies productive variable *)
                             let arg_te =
                               self#type_check arg_term (Some (with_productivity false arg_ty))
                                 env_data false true
                             in
                             (* both target productivities are valid for nonproductive actual
                                argument *)
                             let pr_target_arg_te = match pr_target with
                               | Some pr_target -> TargetEnvms.retarget pr_target arg_te
                               | None -> TargetEnvms.empty
                             in
                             let np_target_arg_te = match np_target with
                               | Some np_target -> TargetEnvms.retarget np_target arg_te
                               | None -> TargetEnvms.empty
                             in
                             TargetEnvms.union pr_target_arg_te np_target_arg_te
                         in
                         TargetEnvms.union pr_arg_te np_arg_te
                       else
                         (* case when target argument is nonproductive *)
                         (* nonproductive target argument implies nonproductive actual argument
                            and no productive vars *)
                         let arg_te =
                           self#type_check arg_term (Some arg_ty) env_data true false
                         in
                         (* both target productivities are valid for nonproductive target
                            argument *)
                         let pr_target_arg_te = match pr_target with
                           | Some pr_target -> TargetEnvms.retarget pr_target arg_te
                           | None -> TargetEnvms.empty
                         in
                         let np_target_arg_te = match np_target with
                           | Some np_target -> TargetEnvms.retarget np_target arg_te
                           | None -> TargetEnvms.empty
                         in
                         TargetEnvms.union pr_target_arg_te np_target_arg_te
                     in
                     let intersection = TargetEnvms.intersect te arg_te in
                     print_verbose !Flags.verbose_proofs @@ lazy (
                       "retargeted envs for the argument: " ^
                       TargetEnvms.to_string arg_te ^ "\n" ^
                       "intersected with envs: " ^
                       TargetEnvms.to_string te ^ "\n" ^
                       "env count for the argument: " ^
                       string_of_int (TargetEnvms.size arg_te) ^ "\n" ^
                       "env count after intersection: " ^
                       string_of_int (TargetEnvms.size intersection) ^ "\n"
                     );
                     (* Productive target might require duplication in (3), but this can only
                        be checked at the end. (or TODO optimization in argument order).
                        Nonproductive target requires no duplication. *)
                     let res = TargetEnvms.filter_no_dup_for_np_targets intersection in
                     print_verbose !Flags.verbose_proofs @@ lazy (
                       "env count after no duplication filtering: " ^
                       string_of_int (TargetEnvms.size res) ^ "\n"
                     );
                     indent (-1);
                     res
                  )
             )
         in
         print_verbose !Flags.verbose_proofs @@ lazy (
           "* Intersected envs before duplication filtering:\n" ^
           "  " ^ TargetEnvms.to_string te ^ "\n"
         );
         let te =
           if not head_pr then
             begin
               (* a duplication or productive actual argument is required when head is not
                  productive and target is productive *)
               let te = TargetEnvms.filter_dup_or_pr_arg_for_pr_targets te in
               print_verbose !Flags.verbose_proofs @@ lazy (
                 "* env count after duplication or pr arg filtering: " ^
                 string_of_int (TargetEnvms.size te) ^ "\n";
               );
               te
             end
           else
             te
         in
         if force_pr_var then
           let te = TargetEnvms.filter_pr_vars te in
           print_verbose !Flags.verbose_proofs @@ lazy (
             "* env count after pr var filtering: " ^
             string_of_int (TargetEnvms.size te) ^ "\n"
           );
           indent (-1);
           te
         else
           begin
             indent (-1);
             te
           end
       )
    )

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
