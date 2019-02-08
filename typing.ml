open Cfa
open GrammarCommon
open HGrammar
open Type

(** A single possible typing of variables mapping variables to their types, treated as if there
    was AND as the delimiter. *)
type venv = (var_id * ity) list

(** List of possible typings of variables, treated as if there was OR as the delimiter. *)
type venvl = venv list

module TySet = Set.Make(Ty)

class typing (hgrammar : hgrammar) (cfa : cfa) = object(self)
  (* --- registers --- *)
                     
  (** nt_ity[nt] has all typings of nonterminal nt. *)
  val nt_ity : ity array = [||]

  (* --- utility --- *)

  method nt_ty_exists (nt : nt_id) (ty : ty) : bool =
    TyList.exists (fun nt_ty -> nt_ty = ty) nt_ity.(nt)

  (* --- typing --- *)
  
  method terminal_ity : terminal -> ity =
    let np = TyList.singleton NP in
    let pr = TyList.singleton PR in
    let a_ity = TyList.of_list [
        mk_fun_ty np PR;
        mk_fun_ty pr PR
      ] in
    let b_ity = TyList.of_list [
        mk_fun_ty np (mk_fun_ty TyList.empty NP);
        mk_fun_ty pr (mk_fun_ty TyList.empty NP);
        mk_fun_ty TyList.empty (mk_fun_ty np NP);
        mk_fun_ty TyList.empty (mk_fun_ty pr NP)
      ] in
    let e_ity = TyList.singleton NP in
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
      with some restrictions. If t = NP then t = np, but any * are valid without additional
      information. If t = PR then t = pr or at least one of * is pr. However, if head is not a
      productive variable then at least two of * are pr. *)
  method filter_compatible_heads (head_is_var : bool) (ity : ity) (arity : int) (target : ty) : ity =
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
            ) 0 arg_itys >= if head_is_var then 1 else 2
        ) ity
    else
      TyList.filter (fun ty ->
          let res_ty = remove_args ty arity in
          eq_ty res_ty target
        ) ity

  (** Creates a list of arrays of pairs (term, ity) with ity being intersection type for given
      argument, and each element of outer list corresponds to one of provided types.
      Combines that in a tuple with a boolean whether the whole type is productive. *)
  method annotate_args : 'a. 'a list -> ity -> (('a * ity) array * bool) list = fun terms ity ->
    let rec annotate_args_ty terms ty acc =
      match terms, ty with
      | term :: terms', Fun (_, ity, ty') ->
        annotate_args_ty terms' ty' ((term, ity) :: acc)
      | [], _ ->
        (Array.of_list (List.rev acc), is_productive ty)
      | _ -> failwith "List of terms longer than list of arguments"
    in
    TyList.map (fun ty ->
        annotate_args_ty terms ty []
      ) ity
        
  (** Merges vtes (variable types) by combining the list of type bindings in order, and combining
      types when a binding for the same variable is present in both lists. The resulting binding
      is ordered ascendingly lexicographically by variable ids. Combining types is also idempodently
      merging list of types (i.e., there are sets of types). TODO redo docs from old ones *)
  method intersect_two_venvs (venv1 : venv) (venv2 : venv) : venv =
    match venv1, venv2 with
    | [], _ -> venv2
    | _, [] -> venv1
    | ((v1, ity1) :: venv1', (v2, ity2) :: venv2') ->
      let n = compare v1 v2 in
      if n < 0 then
        (v1, ity1) :: (self#intersect_two_venvs venv1' venv2)
      else if n > 0 then
        (v2, ity2) :: (self#intersect_two_venvs venv1 venv2')
      else
        (v1, TyList.merge ity1 ity2) :: (self#intersect_two_venvs venv1' venv2')

  (** Flatten an intersection of variable environment lists, which are OR-separated lists of
      AND-separated lists of typings of unique in inner list variables. Flattening means moving
      outer intersection (AND) inside. *)
  method intersect_two_venvls (venvl1 : venvl) (venvl2 : venvl) : venvl =
    match venvl1, venvl2 with
    | _, [] -> [] (* second typing is invalid *)
    | [], _-> [] (* first typing is invalid *)
    | _, [[]] -> venvl1 (* no variables in second typing *)
    | [[]], _ -> venvl2 (* no variables in first typing *)
    | _ ->
      List.fold_left
        (fun acc venv1 ->
           let venvl2' = List.rev_map (fun venv2 ->
               self#intersect_two_venvs venv1 venv2
             ) venvl2
           in
           List.rev_append venvl2' acc)
        [] venvl1

  method intersect_venvls (venvls : venvl list) : venvl =
    match venvls with
    | [] -> [[]]
    | [venvl] -> venvl
    | venvl :: venvs' ->
      self#intersect_two_venvls venvl (self#intersect_venvls venvs')

  (* TODO this should be done on hterm, not term *)
  method infer_wo_venv (hterm : hterm) (target : ty)
      (no_pr_vars : bool) (force_pr_var : bool) : venvl =
    assert (not (no_pr_vars && force_pr_var));
    match hterm with
    | HT a, [] ->
      if TyList.exists (fun ty -> eq_ty target ty) (self#terminal_ity a) && not force_pr_var then
        [[]]
      else
        []
    | HNT nt, [] ->
      if self#nt_ty_exists nt target && not force_pr_var then
        [[]]
      else
        []
    | HVar x, [] ->
      if is_productive target then
        [] (* variables are only NP *)
      else if no_pr_vars then
        [[(x, TyList.singleton target)]]
      else if force_pr_var then
        [[(x, TyList.singleton (with_productivity target PR))]]
      else
        (* both NP and PR versions are possible *)
        [
          [(x, TyList.singleton target)];
          [(x, TyList.singleton (with_productivity target PR))]
        ]
    | _ -> (* application *)
      let h, args = hgrammar#decompose_hterm hterm in
      self#infer_app_wo_env h args target no_pr_vars force_pr_var

  (** To be used only on terms without head variables. *)
  method infer_app_wo_env (h : head) (args : hterm list) (target : ty)
      (no_pr_vars : bool) (force_pr_var : bool) : venvl =
    let h_arity = List.length args in
    (* Get all h typings *)
    let all_h_ity = self#infer_head_ity h in
    (* filtering compatible head types assuming head is not a variable *)
    let h_ity = self#filter_compatible_heads false all_h_ity h_arity target in
    let h_ity = self#annotate_args args h_ity in
    (* TODO optimizations:
       * caching argument index * argument required productivity -> venvl
       * computing terms without variables first and short circuit after for all terms
       * computing terms with non-duplicating variables last
       * pre-computing order of computing argument types
       * maybe cache with versioning or just cache of all typings
       * flag to choose optimization in order to benchmark them later *)
    let target_pr = is_productive target in
    List.concat (List.map (fun (args, head_pr) ->
        let venvl = Array.fold_left (fun acc (arg_term, arg_ity) ->
            (* typing arg_term : arg_ity with short-circuit *)
            if acc = [] then
              acc
            else
              self#intersect_two_venvls acc (TyList.fold_left (fun acc arg_ty ->
                  if acc = [] then
                    acc
                  else
                    let arg_pr = is_productive arg_ty in
                    (* When argument is productive in head type, it can be either productive or
                       not productive with a productive variable. When argument is not productive
                       in head type, it must be not productive and have no productive variables. *)
                    (* TODO refactor - split by productivity, not flipping *)
                    let venvl_direct =
                      if arg_pr || not force_pr_var then
                        self#infer_wo_venv arg_term arg_ty
                          (no_pr_vars || not arg_pr) force_pr_var
                      else
                        []
                    in
                    let venvl_flipped =
                      if arg_pr && not no_pr_vars then
                        self#infer_wo_venv arg_term (flip_productivity arg_ty) false true
                      else
                        []
                    in
                    self#intersect_two_venvls (List.rev_append venvl_flipped venvl_direct) acc
                ) acc arg_ity)
          ) [[]] args
        in
        (* Note that below productive argument describes productivity of the argument term, not
           productivity of the argument in head's type. *)
        if target_pr then
          (* When the target is productive, there are three options:
             * head is productive and there are no restrictions on arguments, or
             * head is not productive and at least one argument is productive, or
             * head is not productive and all arguments are not productive and there is a
               duplication (which implies that at least two arguments are productive in head type
               assuming no head variables). *)
          []
        else
          (* When the target is not productive, the head is not productive, no arguments are
             productive, and there are no duplications. There still can be productive arguments in
             head's type, as long as that does not force a duplication. *)
          []
      ) h_ity)
    (*
    List.iter (fun h_ity ->
        List.iter (fun (_, h_arg_itys) ->
            List.iter (fun (i, ity) ->
                arg_itys_sums.(i) <- TyList.fold_right TySet.add ity arg_itys_sums.(i)
              ) h_arg_itys
          ) h_ity
      ) [pr_h_ity; np_h_ity];
    (* then type arguments without variables to remove all impossible typings *)
    (* TODO use hterms which have free contains_vars_in_term info *)
    let terms_wo_vars_ixs = List.filter (fun i -> i >= 0)
        (List.mapi (fun i term ->
             if contains_vars_in_term terms.(i) then
               -1
             else
               i
           ) terms_list)
    in
    List.iter (fun i ->
        let term = terms.(i) in
        arg_itys_sums.(i) <- TySet.filter (fun ty ->
            (* the no_pr_vars flag does not matter where there are no variables *)
            infer_wo_venv term ty true = [[]]
          ) arg_itys_sums.(i)
      ) terms_wo_vars_ixs;
    (* removing impossible typings *)
    let filter_h_ity h_ity =
      List.filter (fun (_, h_arg_itys) ->
          List.for_all (fun (i, h_arg_ity) ->
              TyList.for_all (fun ty -> TySet.mem ty arg_itys_sums.(i)) h_arg_ity
            ) h_arg_itys
        ) h_ity in
    let pr_h_ity = filter_h_ity pr_h_ity in
    let np_h_ity = filter_h_ity np_h_ity in
    (* head has empty variable environment, since there are no head variables - proceeding to
       computing variable environments and typings of arguments *)
    let pr_app = is_productive target in
    if pr_app then
      begin
        []
        (* TODO type args as np or pr, all from pr_h_ity with no restrictions *)
        (* type np_h_ity with restriction that there has to be a duplication - skip all cases where
           everything is not duplicating and term with last variable appearing 2+ times is analyzed
           in particular, it is good to leave terms with variables present only in them for last -
           maybe sort the order of checking by the amount of duplicated variables? *)
        (* cache typing for each term *)
      end
    else
      (* cache arg_ix * ty -> venvl or better hterm_id *)
      begin
        (* No variables nor arguments can be productive when the application is nonproductive. *)
        (* Each element of the list contains possible environments for one typing of the head.
           A sum of these environments is all possible environments for given target. *)
        let h_venvls = List.map (fun (_, h_arg_itys) ->
            (* Each element of the list contains possible environments for one of the arguments.
               For the whole application to work, one environment from each one has to be
               intersected with the rest in all possible combinations. *)
            let app_venvls = List.map (fun (i, ity) ->
                (* Each element of the list contains possible environments for one of the
                   typings in the intersection type, so exactly one possibility from each has
                   to be taken and intersected. *)
                let arg_venvls : venvl list = TyList.map (fun ty ->
                    (* venvs for one type of the arg *)
                    self#infer_wo_venv terms.(i) ty true
                  ) ity
                in
                arg_venvls
              ) h_arg_itys
            in
            let venvls_to_intersect = List.flatten app_venvls in
            self#intersect_venvls venvls_to_intersect
          ) np_h_ity
        in
        List.flatten h_venvls
      end
(*
      for i = 0 to Array.length terms - 1 do
        (* TODO type args as forced np *)
        (* make product of variables for each arg ity *)
        (* sum the result from different arg itys *)
      done;
*)
      (* type all nonproductive arguments first, since it has more restrictions and is faster *)
      (* then type all productive arguments *)
*)

  (* --- printing --- *)

  method print_ty (ty : ty) =
    match ty with
    | PR -> print_string "pr"
    | NP -> print_string "np"
    | Fun (_, ity, ty) ->
      print_string "(";
      self#print_ity ity;
      print_string "->";
      self#print_ty ty;
      print_string ")"
        
  method print_ity_l (ity : ty list) =
    match ity with
    | [] -> print_string "top"
    | [ty] -> self#print_ty ty
    | ty::ity' ->
      self#print_ty ty;
      print_string "^";
      self#print_ity_l ity'

  method print_ity (ity : ity) =
    self#print_ity_l (TyList.to_list ity)
      
  method print_itys (itys : ity array) =
    Array.iter (fun ity ->
        self#print_ity ity;
        print_string " * "
      ) itys

  method print_itylist (ity : ity) =
    TyList.iter (fun ty ->
        self#print_ty ty;
        print_string "\n"
      ) ity

  method print_nt_ity =
    print_string "Types of nt:\n============\n";
    for nt = 0 to (Array.length nt_ity) - 1 do
      print_string ((hgrammar#nt_name nt)^":\n");
      self#print_itylist nt_ity.(nt)
    done
end
