open Cfa
open GrammarCommon
open HGrammar
open Type

(** A single possible typing of variables mapping variables to their types, treated as if there
    was AND as the delimiter. *)
module VEnv = SortedList.Make(struct
    type t = var_id * ity
    let compare (x_id, _) (y_id, _) = Pervasives.compare x_id y_id
  end)

(** List of possible typings of variables, treated as if there was OR as the delimiter. *)
type venvl = VEnv.t list

(** Variable environment along with flags whether there was a duplication during its
    construction and whether a productive argument was used. *)
type venvf = VEnv.t * bool * bool

(** List of variable environments with duplication flags. *)
type venvfl = venvf list

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
        
  (** Merges vtes (variable types) by combining the list of type bindings in order, and combining
      types when a binding for the same variable is present in both lists. The resulting binding
      is ordered ascendingly lexicographically by variable ids. Combining types is also idempodently
      merging list of types (i.e., there are sets of types). TODO redo docs from old ones *)
  method intersect_two_venvs (venv1, dup1, pruse1 : venvf) (venv2, dup2, pruse2 : venvf) : venvf =
    let duplication = ref (dup1 || dup2) in
    let intersection = VEnv.merge_custom (fun (v1, ity1) (v2, ity2) ->
        (v1, TyList.merge_custom (fun x _ ->
             duplication := true;
             x
           ) ity1 ity2)
      ) venv1 venv2
    in
    (intersection, !duplication, pruse1 || pruse2)

  (** Flatten an intersection of variable environment lists, which are OR-separated lists of
      AND-separated lists of typings of unique in inner list variables. Flattening means moving
      outer intersection (AND) inside. Return if there was a duplication. *)
  method intersect_two_venvls (venvl1 : venvfl) (venvl2 : venvfl) : venvfl =
    match venvl1, venvl2 with
    | _, [] -> [] (* second typing is invalid *)
    | [], _-> [] (* first typing is invalid *)
    | _, [(VEnv.L [], _, _)] ->
      (* no variables in second typing - special case optimization *)
      venvl1
    | [(VEnv.L [], _,  _)], _ ->
      (* no variables in first typing - special case optimization *)
      venvl2
    | _ ->
      List.fold_left
        (fun acc venv1 ->
           let venvl2' = List.rev_map (fun venv2 ->
               self#intersect_two_venvs venv1 venv2
             ) venvl2
           in
           List.rev_append venvl2' acc)
        [] venvl1

  (*
  method intersect_venvls (venvls : venvl list) : venvl =
    match venvls with
    | [] -> [VEnv.empty]
    | [venvl] -> venvl
    | venvl :: venvs' ->
      self#intersect_two_venvls venvl (self#intersect_venvls venvs')
*)

  (*
  method venvl_has_duplication (venvl : venvl) : bool =
    let min_var_id = List.fold_left (fun min_var_id venv ->
        match min_var_id, VEnv.hd_option venv with
        | Some mv, Some (v, _) -> Some (min mv v)
        | mv, None -> mv
        | None, v -> v
      ) None venvl
    in
    match min_var_id with
    | Some mv ->
      let min_var_tys = List.fold_left (fun ity_sum venv ->
          match VEnv.hd_option venv with
          | Some (v, ity) ->
            if v = mv then
              begin
                let eq =
              TyList.merge_custom (fun x _ ->
                    x
                  ) ity_sum ity
            end
            else
              ity_sum
          | None ->
            ity_sum
        ) TyList.empty venvl
      in
      true
    | None -> false
              *)

  (* TODO this should be done on hterm, not term *)
  method infer_wo_venv (hterm : hterm) (target : ty)
      (no_pr_vars : bool) (force_pr_var : bool) : venvl =
    assert (not (no_pr_vars && force_pr_var));
    match hterm with
    | HT a, [] ->
      if TyList.exists (fun ty -> eq_ty target ty) (self#terminal_ity a) && not force_pr_var then
        [VEnv.empty]
      else
        []
    | HNT nt, [] ->
      if self#nt_ty_exists nt target && not force_pr_var then
        [VEnv.empty]
      else
        []
    | HVar x, [] ->
      if is_productive target then
        [] (* variables are only NP *)
      else if no_pr_vars then
        [VEnv.singleton (x, TyList.singleton target)]
      else if force_pr_var then
        [VEnv.singleton (x, TyList.singleton (with_productivity PR target))]
      else
        (* both NP and PR versions are possible *)
        [
          VEnv.singleton (x, TyList.singleton target);
          VEnv.singleton (x, TyList.singleton (with_productivity PR target))
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
    (* Iterate over each possible typing of the head *)
    List.concat (List.map (fun (args, head_pr) ->
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
        let venvfl = Utilities.fold_left_short_circuit (fun venvfl (arg_term, arg_ity) ->
            (* venvfl contains not only variable environments, but also information whether
               there was a duplication (for (3) and (NP)) and whether a productive argument was
               used (for (3)). *)
            TyList.fold_left_short_circuit (fun venvfl arg_ty ->
                (* venvfl are possible variable environments constructed so far with processed
                   arguments and typings of the current argument *)
                let target_arg_pr = is_productive arg_ty in
                (* When argument is productive in head type, it can be either productive or
                   not productive with a productive variable. When argument is not productive
                   in head type, it must be not productive and have no productive variables. *)
                let arg_venvfl =
                  if target_arg_pr then
                    (* productive target argument *)
                    let arg_pr_venvfl =
                      if target_pr then
                        (* productive argument *)
                        List.map (fun v -> (v, false, true))
                          (self#infer_wo_venv arg_term arg_ty no_pr_vars false)
                        (* TODO check force_pr_var after everything *)
                      else
                        []
                    in
                    let arg_np_venvfl =
                      if no_pr_vars then
                        []
                      else
                        (* nonproductive argument with productive variable *)
                        List.map (fun v -> (v, false, false))
                          (self#infer_wo_venv arg_term (with_productivity NP arg_ty) false true)
                    in
                    List.rev_append arg_pr_venvfl arg_np_venvfl
                  else
                    (* nonproductive target argument (which implies nonproductive argument) *)
                    List.map (fun v -> (v, false, false))
                      (self#infer_wo_venv arg_term arg_ty true false)
                in
                let intersection = self#intersect_two_venvls venvfl arg_venvfl in
                if target_pr then
                  (* pr target might require duplication in (3), but this can only be checked at
                     the end (or TODO optimization in argument order) *)
                  intersection
                else
                  (* np target requires no duplication *)
                  List.filter (fun (_, dup, _) -> not dup) intersection
              ) venvfl arg_ity []
          ) [(VEnv.empty, false, false)] args []
        in
        let venvfl =
          if target_pr then
            List.filter (fun (_, dup, pruse) -> dup || pruse)
              venvfl
          else
            venvfl
        in
        let venvl = List.map (fun (venv, _, _) -> venv) venvfl in
        if force_pr_var then
          List.filter (fun venv ->
              VEnv.exists (fun (_, ity) -> TyList.exists is_productive ity) venv
            ) venvl
        else
          venvl
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
