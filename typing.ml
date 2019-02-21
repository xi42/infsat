open Binding
open Cfa
open Environment
open GrammarCommon
open HGrammar
open Type
open HtyStore

class typing (hgrammar : hgrammar) (cfa : cfa) = object(self)
  (* --- registers --- *)

  (** nt_ity[nt] has all typings of nonterminal nt. *)
  val nt_ity : ity array = Array.make hgrammar#nt_count TyList.empty

  (** htys[id] contains list of types derived under some environment for
      corresponding terms in the list of terms identified by id. *)
  val htys : hty_store = new hty_store hgrammar

  (* --- printing --- *)
  
  (** Used only for verbose printing; global in order to not pass additional argument when not
      verbose printing. *)
  val mutable indent = 0

  (* --- direct manipulation on registers --- *)

  method nt_ty_exists (nt : nt_id) (ty : ty) : bool =
    TyList.exists (fun nt_ty -> nt_ty = ty) nt_ity.(nt)

  method add_nt_ty (nt : nt_id) (ty : ty) =
    nt_ity.(nt) <- TyList.merge nt_ity.(nt) (TyList.singleton ty)

  (* --- generating envs --- *)

  (** Returns venvs where each venv in envs is prepended with exactly one ty from tys in every
      combination. *)
  method private mk_prod_hty_bindings (i, j : int * int) (prefixes : hty list)
      (postfixes : hty binding list) (acc : hty binding list) : hty binding list =
    match prefixes with 
    | [] -> acc
    | prefix :: prefixes' ->
      let acc' = List.fold_left (fun acc postfix ->
          ((i, j, prefix) :: postfix) :: acc
        ) acc postfixes
      in
      self#mk_prod_hty_bindings (i, j) prefixes' postfixes acc'

  (* env is a list of elements of the form (i,j,id), 
     which means that variables i to j are bound to ti to tj,
     where id is the identifier of [ti;...;tj] *)
  method mk_hty_bindings : hterms_id binding -> hty binding list = function
    | [] -> [[]]
    | [(i, j, id)] ->
      let htys = htys#get_htys id in 
      List.map (fun hty -> [(i, j, hty)]) htys
    | (i, j, id) :: bindings' ->
      match htys#get_htys id with
      | [] -> []
      | htys ->
        (* recursively get all bindings without using current application info *)
        match self#mk_hty_bindings bindings' with
        | [] -> []
        | hty_bindings ->
          (* Make product with the current application info - each typing of hterm with
             identifier id is valid for range i-j, so the output is all possible bindings
             constructed by prepending one of possible types for i-j to any of current bindings.
             This may blow up the number of possible type bindings. *)
          self#mk_prod_hty_bindings (i, j) htys hty_bindings []

  (* --- typing --- *)
  
  method terminal_ity : terminal -> ity =
    let np = TyList.singleton NP in
    let pr = TyList.singleton PR in
    let a_ity = TyList.of_list [
        mk_fun np PR;
        mk_fun pr PR
      ] in
    let b_ity = TyList.of_list [
        mk_fun np (mk_fun TyList.empty NP);
        mk_fun pr (mk_fun TyList.empty NP);
        mk_fun TyList.empty (mk_fun np NP);
        mk_fun TyList.empty (mk_fun pr NP)
      ] in
    let e_ity = np in
    function
    | A -> a_ity
    | B -> b_ity
    | E -> e_ity

  (** Returns sorted list of typings available for given head term. *)
  method infer_head_ity (h : head) : ity =
    match h with
    | HNT nt -> nt_ity.(nt)
    | HVar x -> failwith "TODO"
    | HT a -> self#terminal_ity a

  method is_nonproductive_app_head_ty (ty : ty) (arity : int) : bool =
    let arg_itys, res_ty = ty2list ty arity in
    not (is_productive res_ty) &&
    not (List.exists (fun ity -> TyList.exists is_productive ity) arg_itys)

  (** Assume that the target is
      /\_i t_1i -> .. -> /\_i t_ki -> t
      with t = pr or np. Typings of h that could make the application have the target type are
      * -> .. -> * -> /\_i t_1i -> .. -> /\_i t_ki -> *
      with some restrictions. If target = NP then t = np, but any * could be valid without
      additional information about duplication. If t = PR then t = pr or at least one of * is
      pr. *)
  method filter_compatible_heads (ity : ity) (arity : int) (target : ty) : ity =
    if is_productive target then
      let flipped_target = flip_productivity target in
      TyList.filter (fun ty ->
          let arg_itys, res_ty = ty2list ty arity in
          eq_ty res_ty target ||
          eq_ty res_ty flipped_target &&
          List.fold_left (fun acc ity ->
              TyList.fold_left (fun acc ty ->
                  if is_productive ty then
                    acc + 1
                  else
                    acc
                ) acc ity
            ) 0 arg_itys >= 1
        ) ity
    else
      TyList.filter (fun ty ->
          let res_ty = remove_args ty arity in
          eq_ty res_ty target
        ) ity

  (** Creates a list of arrays of pairs (term, ity) with ity being intersection type for given
      argument, and each element of outer list corresponds to one of provided types.
      Combines that in a tuple with a boolean whether the whole type is productive. *)
  method annotate_args : 'a. 'a list -> ity -> (('a * ity) list * bool) list = fun terms ity ->
    let rec annotate_args_ty terms ty acc =
      match terms, ty with
      | term :: terms', Fun (_, ity, ty') ->
        annotate_args_ty terms' ty' ((term, ity) :: acc)
      | [], _ ->
        (List.rev acc, is_productive ty)
      | _ -> failwith "List of terms longer than list of arguments"
    in
    TyList.map (fun ty ->
        annotate_args_ty terms ty []
      ) ity
        
  (** Infer variable environments under which type checking of hterm : ty succeeds. Assume no head
      variables are present and infer type of each variable based on the type of the head that is
      applied to it.
      Flag no_pr_vars prevents inference of productive variables. Flag force_pr_var ensures that
      there is at least one productive variable is inferred. Only one of these flags may be true.
  *)
  method infer_wo_env (hterm : hterm) (target : ty)
      (no_pr_vars : bool) (force_pr_var : bool) : envl =
    assert (not (no_pr_vars && force_pr_var));
    if !Flags.verbose then
      begin
        let vars_info = match no_pr_vars, force_pr_var with
          | true, false -> " (no pr vars)"
          | false, true -> " (force pr var)"
          | _ -> ""
        in
        print_string @@ String.make indent ' ' ^ "Type checking " ^
                        hgrammar#string_of_hterm hterm ^ " : " ^ string_of_ty target ^
                        vars_info ^ "\n"
      end;
    let res = match hterm with
      | HT a, [] ->
        if TyList.exists (fun ty -> eq_ty target ty) (self#terminal_ity a) && not force_pr_var then
          [Env.empty]
        else
          []
      | HNT nt, [] ->
        if self#nt_ty_exists nt target && not force_pr_var then
          [Env.empty]
        else
          []
      | HVar x, [] ->
        if is_productive target then
          [] (* variables are only NP *)
        else if no_pr_vars then
          [Env.singleton (x, TyList.singleton target)]
        else if force_pr_var then
          [Env.singleton (x, TyList.singleton (with_productivity PR target))]
        else
          (* both NP and PR versions are possible *)
          [
            Env.singleton (x, TyList.singleton target);
            Env.singleton (x, TyList.singleton (with_productivity PR target))
          ]
      | _ -> (* application *)
        let h, args = hgrammar#decompose_hterm hterm in
        self#infer_app_wo_env h args target no_pr_vars force_pr_var
    in
    if !Flags.verbose then
      begin
        print_string @@ String.make indent ' ' ^
                        hgrammar#string_of_hterm hterm ^ " : " ^ string_of_ty target;
        match res with
        | [] -> print_string " does not type check\n"
        | _ -> print_string @@ " type checks under " ^ string_of_envl res ^ "\n"
      end;
    res

  (** To be used only on terms without head variables. *)
  method infer_app_wo_env (h : head) (args : hterm list) (target : ty)
      (no_pr_vars : bool) (force_pr_var : bool) : envl =
    let h_arity = List.length args in
    (* Get all h typings *)
    let all_h_ity = self#infer_head_ity h in
    (* filtering compatible head types assuming head is not a variable *)
    let h_ity = self#filter_compatible_heads all_h_ity h_arity target in
    if !Flags.verbose then
      begin
        print_string @@ String.make indent ' ' ^ "head_ity " ^ string_of_ity all_h_ity ^ "\n";
        print_string @@ String.make indent ' ' ^ "compatible head_ity " ^ string_of_ity h_ity ^
                        "\n"
      end;
    let h_ity = self#annotate_args args h_ity in
    (* TODO optimizations:
       * caching argument index * argument required productivity -> envl
       * computing terms without variables first and short circuit after for all terms
       * computing terms with non-duplicating variables last with short-circuiting when
         duplication is expected
       * pre-computing order of computing argument types
       * maybe cache with versioning or just cache of all typings
       * flag to choose optimization in order to benchmark them later *)
    let target_pr = is_productive target in
    (* Iterate over each possible typing of the head *)
    List.concat (List.map (fun (args, head_pr) ->
        if !Flags.verbose then
          begin
            print_string @@ String.make indent ' ' ^ "* Type checking " ^
                            String.concat " -> " @@ List.map (fun (arg_term, arg_ity) ->
                "(" ^ hgrammar#string_of_hterm arg_term ^ " : " ^ string_of_ity arg_ity ^ ")"
              ) args;
            if head_pr then
              print_string " -> ... -> pr\n"
            else
              print_string " -> ... -> np\n";
            indent <- indent + 2
          end;
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
        let envfl = Utilities.fold_left_short_circuit (fun envfl (arg_term, arg_ity) ->
            (* envfl contains not only variable environments, but also information whether
               there was a duplication (for (3) and (NP)) and whether a productive argument was
               used (for (3)). *)
            TyList.fold_left_short_circuit (fun envfl arg_ty ->
                if !Flags.verbose then
                  begin
                    print_string @@ String.make indent ' ' ^ "* Typing " ^
                                    hgrammar#string_of_hterm arg_term ^ " : " ^
                                    string_of_ity arg_ity ^ "\n";
                    indent <- indent + 2
                  end;
                (* envfl are possible variable environments constructed so far with processed
                   arguments and typings of the current argument *)
                let target_arg_pr = is_productive arg_ty in
                (* When argument is productive in head type, it can be either productive or
                   not productive with a productive variable. When argument is not productive
                   in head type, it must be not productive and have no productive variables. *)
                let arg_envfl =
                  if target_arg_pr then
                    (* productive target argument *)
                    let arg_pr_envfl =
                      if target_pr then
                        (* productive argument *)
                        List.map (fun v -> (v, false, true))
                          (self#infer_wo_env arg_term arg_ty no_pr_vars false)
                      else
                        []
                    in
                    let arg_np_envfl =
                      if no_pr_vars then
                        []
                      else
                        (* nonproductive argument with productive variable *)
                        List.map (fun v -> (v, false, false))
                          (self#infer_wo_env arg_term (with_productivity NP arg_ty) false true)
                    in
                    List.rev_append arg_pr_envfl arg_np_envfl
                  else
                    (* nonproductive target argument (which implies nonproductive argument) *)
                    List.map (fun v -> (v, false, false))
                      (self#infer_wo_env arg_term arg_ty true false)
                in
                let intersection = intersect_two_envfls envfl arg_envfl in
                if !Flags.verbose then
                  begin
                    indent <- indent - 2;
                    print_string @@ String.make indent ' ' ^ "  env count for the argument: " ^
                                    string_of_int (List.length arg_envfl) ^ "\n";
                    print_string @@ String.make indent ' ' ^ "  env count after intersection: " ^
                                    string_of_int (List.length intersection) ^ "\n"
                  end;
                if target_pr then
                  (* pr target might require duplication in (3), but this can only be checked at
                     the end (or TODO optimization in argument order) *)
                  intersection
                else
                  begin
                    (* np target requires no duplication *)
                    let res = List.filter (fun (_, dup, _) -> not dup) intersection in
                    if !Flags.verbose then
                      print_string @@ String.make indent ' ' ^
                                      "  env count after no duplication filtering: " ^
                                      string_of_int (List.length res) ^ "\n";
                    res
                  end
              ) envfl arg_ity []
          ) [(Env.empty, false, false)] args []
        in
        if !Flags.verbose then
          begin
            print_string @@ String.make indent ' ' ^
                            "* Intersected envs before duplication filtering:\n";
            List.iter (fun (env, dup, pruse) ->
                print_string @@ String.make indent ' ' ^ "  * (dup: " ^
                                Utilities.string_of_bool dup ^ ", prarg: " ^
                                Utilities.string_of_bool pruse ^ ") " ^
                                string_of_env env ^ "\n";
              ) envfl
          end;
        let envfl =
          if target_pr && not head_pr then
            begin
              let res = List.filter (fun (_, dup, pruse) -> dup || pruse) envfl in
              if !Flags.verbose then
                print_string @@ String.make indent ' ' ^
                                "* env count after duplication or pr arg filtering: " ^
                                string_of_int (List.length res) ^ "\n";
              res
            end
          else
            envfl
        in
        let envl = List.map (fun (env, _, _) -> env) envfl in
        if force_pr_var then
          let res = List.filter (fun env ->
              Env.exists (fun (_, ity) -> TyList.exists is_productive ity) env
            ) envl
          in
          if !Flags.verbose then
            begin
              print_string @@ String.make indent ' ' ^ "* env count after pr var filtering: " ^
                              string_of_int (List.length res) ^ "\n";
              indent <- indent - 2
            end;
          res
        else
          begin
            indent <- indent - 2;
            envl
          end
      ) h_ity)

  (* --- printing --- *)

  method print_itylist (ity : ity) =
    TyList.iter (fun ty ->
        print_string @@ string_of_ty ty ^ "\n"
      ) ity

  method print_nt_ity =
    print_string @@ "Types of nt:\n" ^
                    "============\n";
    for nt = 0 to (Array.length nt_ity) - 1 do
      print_string @@ hgrammar#nt_name nt ^ ":\n";
      self#print_itylist nt_ity.(nt)
    done

  (* --- debugging --- *)

  method get_htys = htys
end
