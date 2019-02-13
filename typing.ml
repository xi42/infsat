open Cfa
open GrammarCommon
open HGrammar
open Type

(** A single possible typing of variables mapping variables to their types, treated as if there
    was AND as the delimiter. *)
module VEnv = struct
  include SortedList.Make(struct
    type t = var_id * ity
    let compare (id1, _) (id2, _) = Pervasives.compare id1 id2
  end)

  (** Merge works differently here, since types are not part of the compare function and need to
      be merged manually. Also, information about duplication of productive variables is needed. *)
  let merge_with_dup_info v1 v2 : t * bool =
    let dup = ref false in
    let res = merge_custom (fun (id1, ity1) (_, ity2) ->
        let merged_ity = TyList.merge_custom (fun ty _ ->
            if is_productive ty then
              dup := true;
            ty
          ) ity1 ity2
        in
        (id1, merged_ity)
      ) v1 v2
    in
    (res, !dup)

  let merge v1 v2 = fst @@ merge_with_dup_info v1 v2
end

type venv = VEnv.t

(** List of possible typings of variables, treated as if there was OR as the delimiter. *)
type venvl = venv list

(** Variable environment along with flags whether there was a duplication during its
    construction and whether a productive argument was used. *)
type venvf = venv * bool * bool

(** List of variable environments with duplication flags. *)
type venvfl = venvf list

module TySet = Set.Make(Ty)

let string_of_venvl (venvl : venvl) : string =
  Utilities.string_of_list (VEnv.to_string (fun ((nt, vix), ity) ->
      string_of_int nt ^ "-" ^ string_of_int vix ^ " : " ^ string_of_ity ity
    )) venvl

(** List of variable environments does not need to be sorted during computations, but it is useful
    for unique representation when testing. *)
let sort_venvl (venvl : venvl) : venvl =
  List.sort (VEnv.compare_custom (fun (id1, ity1) (id2, ity2) ->
      let res = Pervasives.compare id1 id2 in
      if res = 0 then
        TyList.compare ity1 ity2
      else
        res
    )) venvl

class typing (hgrammar : hgrammar) (cfa : cfa) = object(self)
  (* --- registers --- *)

  (** nt_ity[nt] has all typings of nonterminal nt. *)
  val nt_ity : ity array = Array.make hgrammar#nt_count TyList.empty

  (* --- utility --- *)

  method nt_ty_exists (nt : nt_id) (ty : ty) : bool =
    TyList.exists (fun nt_ty -> nt_ty = ty) nt_ity.(nt)

  (* --- direct manipulation on registers --- *)

  method add_nt_ty (nt : nt_id) (ty : ty) =
    nt_ity.(nt) <- TyList.merge nt_ity.(nt) (TyList.singleton ty)

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
        
  (** Merges vtes (variable types) by combining the list of type bindings in order, and combining
      types when a binding for the same variable is present in both lists. The resulting binding
      is ordered ascendingly lexicographically by variable ids. Combining types is also idempodently
      merging list of types (i.e., there are sets of types). TODO redo docs from old ones *)
  method intersect_two_venvs (venv1, dup1, pruse1 : venvf) (venv2, dup2, pruse2 : venvf) : venvf =
    let dup_args = dup1 || dup2 in
    let intersection, dup = VEnv.merge_with_dup_info venv1 venv2 in
    (intersection, dup_args || dup, pruse1 || pruse2)

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

  (** Infer variable environments under which type checking of hterm : ty succeeds. Assume no head
      variables are present and infer type of each variable based on the type of the head that is
      applied to it.
      Flag no_pr_vars prevents inference of productive variables. Flag force_pr_var ensures that
      there is at least one productive variable is inferred. Only one of these flags may be true.
  *)
  method infer_wo_venv (hterm : hterm) (target : ty)
      (no_pr_vars : bool) (force_pr_var : bool) : venvl =
    assert (not (no_pr_vars && force_pr_var));
    if !Flags.verbose then
      begin
        let vars_info = match no_pr_vars, force_pr_var with
          | true, false -> " (no pr vars)"
          | false, true -> " (force pr var)"
          | _ -> ""
        in
        print_string @@ "Type checking " ^
                        hgrammar#string_of_hterm hterm ^ " : " ^ string_of_ty target ^
                        vars_info ^ "\n"
      end;
    let res = match hterm with
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
    in
    if !Flags.verbose then
      begin
        print_string (hgrammar#string_of_hterm hterm ^ " : " ^ string_of_ty target);
        match res with
        | [] -> print_string " does not type check\n"
        | _ -> print_string (" type checks under " ^ string_of_venvl res ^ "\n")
      end;
    res

  (** To be used only on terms without head variables. *)
  method infer_app_wo_env (h : head) (args : hterm list) (target : ty)
      (no_pr_vars : bool) (force_pr_var : bool) : venvl =
    let h_arity = List.length args in
    (* Get all h typings *)
    let all_h_ity = self#infer_head_ity h in
    if !Flags.verbose then
      print_string @@ "head_ity " ^ string_of_ity all_h_ity ^ "\n";
    (* filtering compatible head types assuming head is not a variable *)
    let h_ity = self#filter_compatible_heads all_h_ity h_arity target in
    if !Flags.verbose then
      print_string @@ "compatible head_ity " ^ string_of_ity h_ity ^ "\n";
    let h_ity = self#annotate_args args h_ity in
    (* TODO optimizations:
       * caching argument index * argument required productivity -> venvl
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
            print_string "* Type checking ";
            print_string @@ String.concat " -> " @@ List.map (fun (arg_term, arg_ity) ->
                "(" ^ hgrammar#string_of_hterm arg_term ^ " : " ^ string_of_ity arg_ity ^ ")"
              ) args;
            if head_pr then
              print_string " -> ... -> pr\n"
            else
              print_string " -> ... -> np\n"
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
                if !Flags.verbose then
                  print_string @@ "* venv count for the argument: " ^
                                  string_of_int (List.length arg_venvfl) ^ "\n";
                let intersection = self#intersect_two_venvls venvfl arg_venvfl in
                if !Flags.verbose then
                  print_string @@ "* venv count after intersection: " ^
                                  string_of_int (List.length intersection) ^ "\n";
                if target_pr then
                  (* pr target might require duplication in (3), but this can only be checked at
                     the end (or TODO optimization in argument order) *)
                  intersection
                else
                  begin
                    (* np target requires no duplication *)
                    let res = List.filter (fun (_, dup, _) -> not dup) intersection in
                    if !Flags.verbose then
                      print_string @@ "* venv count after no duplication filtering: " ^
                                      string_of_int (List.length res) ^ "\n";
                    res
                  end
              ) venvfl arg_ity []
          ) [(VEnv.empty, false, false)] args []
        in
        let venvfl =
          if target_pr && not head_pr then
            begin
              let res = List.filter (fun (_, dup, pruse) -> dup || pruse) venvfl in
              if !Flags.verbose then
                print_string @@ "* venv count after duplication or pr arg filtering: " ^
                                string_of_int (List.length res) ^ "\n";
              res
            end
          else
            venvfl
        in
        let venvl = List.map (fun (venv, _, _) -> venv) venvfl in
        if force_pr_var then
          let res = List.filter (fun venv ->
              VEnv.exists (fun (_, ity) -> TyList.exists is_productive ity) venv
            ) venvl
          in
          if !Flags.verbose then
            print_string @@ "* venv count after pr var filtering: " ^
                            string_of_int (List.length res) ^ "\n";
          res
        else
          venvl
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
end
