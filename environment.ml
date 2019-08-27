open Binding
open GrammarCommon
open Type

(* --- pure environment --- *)

(** A single possible typing of variables mapping variables to their types, treated as if there
    was AND as the delimiter.
    This structure satisfies the following desired properties:
    - has O(1) access to ity of given var
    - has O(n) merge with another environment *)
class env (var_itys : ity array) = object(self)
  (* --- access --- *)

  method var_count : int = Array.length var_itys

  method get_var_itys : ity array = var_itys

  method get_var_ity (_, i : var_id) : ity = var_itys.(i)

  method mk_fun (codomain : ty) : ty =
    cons_fun (Array.to_list var_itys) codomain

  method mem (v : var_id) (ty : ty) : bool =
    TyList.mem ty @@ self#get_var_ity v

  method compare (env' : env) : int =
    let var_itys' = env'#get_var_itys in
    assert (Array.length var_itys = Array.length var_itys');
    let rec compare_aux (i : int) =
      if i = Array.length var_itys then
        0
      else
        let ci = TyList.compare var_itys.(i) var_itys'.(i) in
        if ci = 0 then
          compare_aux (i + 1)
        else
          ci
    in
    compare_aux 0

  method hash : int =
    Array.fold_left (fun acc x ->
        Hashtbl.hash (acc, Hashtbl.hash @@ List.map Ty.id_of_ty @@ TyList.to_list x)
      ) 0 var_itys

  method has_pr_vars : bool =
    Array.exists (fun ity -> TyList.exists is_productive ity) var_itys

  (* --- manipulation --- *)

  method set_var_ity (i : int) (ity : ity) =
    var_itys.(i) <- ity
  
  (** Merging environments is summation of itys of the same var. The result is a new, merged
      environment and information whether duplication of a productive variable occured. *)
  method merge (env' : env) : env * bool =
    let var_itys' = env'#get_var_itys in
    assert (Array.length var_itys = Array.length var_itys');
    let var_itys_new = Array.make (Array.length var_itys) TyList.empty in
    let dup = ref false in
    Array.iteri (fun i ity ->
        var_itys_new.(i) <- TyList.merge_custom (fun ty _ ->
            if is_productive ty then
              dup := true;
            ty
          ) ity var_itys'.(i)
      ) var_itys;
    (new env @@ var_itys_new, !dup)

  (* --- printing --- *)
  
  method to_string : string =
    if self#var_count = 0 then
      "*"
    else
      String.concat ", " @@
      List.mapi (fun i ity -> string_of_int i ^ " : " ^ string_of_ity ity) @@
      Array.to_list var_itys
end

let env_eq (env1 : env) (env2 : env) =
  env1#compare env2 = 0

let env_hash (env : env) : int =
  env#hash

let empty_env (var_count : int) : env =
  new env @@ Array.make var_count TyList.empty

let singleton_env (var_count : int) (_, i : var_id) (ity : ity) : env =
  let env = empty_env var_count in
  env#set_var_ity i ity;
  env

let hty_binding2env (var_count : int) (binding : hty binding) : env =
  let itys = Array.make var_count TyList.empty in
  List.iter (fun (i, _, hty) ->
      List.iteri (fun ix ity ->
          itys.(i + ix) <- ity
        ) hty
    ) binding;
  new env itys

let env_compare (env1 : env) (env2 : env) : int = env1#compare env2
