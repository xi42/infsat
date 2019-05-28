open GrammarCommon
open HGrammar
open Type
open TypingCommon
open Utilities

module VarMap = Set.Make (struct
    type t = var_id
    let compare = Pervasives.compare
  end)

module NTTyInitMap = Map.Make (struct
    type t = nt_ty * bool
    let compare = Pervasives.compare
  end)

(* note that var_assumptions is redundant, since it is included in derived *)
type proof = { derived : nt_ty; var_assumptions : ity array;
               nt_assumptions : int HlocMap.t NTTyMap.t;
               t_assumptions : int HlocMap.t TTyMap.t;
               positive : bool; initial : bool}

let proof_compare (ignore_initial : bool) (proof1 : proof) (proof2 : proof) : int =
  compare_pair
    (compare_pair nt_ty_compare @@ NTTyMap.compare Pervasives.compare)
    Pervasives.compare
    ((proof1.derived, proof1.nt_assumptions), (proof1.positive, proof1.initial || ignore_initial))
    ((proof2.derived, proof2.nt_assumptions), (proof2.positive, proof2.initial || ignore_initial))

let string_of_proof (hg : hgrammar) (proof_ids : int NTTyInitMap.t option)
    (proof : proof) : string =
  let nt, ty = proof.derived in
  let proof_id =
    match proof_ids with
    | Some proof_ids ->
      let proof_id = NTTyInitMap.find (proof.derived, proof.initial) proof_ids in
      "(Proof " ^ string_of_int proof_id ^ ")"
    | None -> ""
  in
  let vars_info =
    array_listmap proof.var_assumptions (fun i ity ->
        hg#var_name (nt, i) ^ " : " ^ string_of_ity ity
      )
  in
  let nts_info =
    NTTyMap.bindings proof.nt_assumptions |> List.map (fun ((nt', ty'), locs) ->
        let multi_info =
          if HlocMap.sum locs > 1 then
            " (+)"
          else
            ""
        in
        let proof_id' =
          match proof_ids with
          | Some proof_ids ->
            (* There can still be two kinds of proofs - initial (first) and not.
               First proofs always point at first proofs. Other proofs are proofs of
               path to cycle and cycle itself, with all dependencies. So, the non-first
               proof may point at first proof, but first proof will never point at non-first
               proof unless there is no other choice. *)
            let proof_id' =
              match NTTyInitMap.find_opt ((nt', ty'), proof.initial) proof_ids with
              | Some proof_id' -> proof_id'
              | None ->
                NTTyInitMap.find ((nt', ty'), not proof.initial) proof_ids
            in
            "(" ^ string_of_int proof_id' ^ ") "
          | None -> ""
        in
        proof_id' ^ hg#nt_name nt' ^ " : " ^ string_of_ty ty' ^ multi_info
      )
  in
  let positive_info =
    if proof.positive then
      " (+)"
    else
      ""
  in
  proof_id ^ "\n" ^
  String.concat ",\n" (vars_info @ nts_info) ^
  "\n|- " ^ hg#nt_name nt ^ " = " ^ hg#string_of_hterm false (hg#nt_body nt) ^ " : " ^
  string_of_ty ty ^ positive_info

class cycle_proof (path_to_cycle : (proof * bool) list)
    (cycle : (proof * bool) list) (escape : proof) (proofs : proof list) = object(self)
  (** Numerical identifiers of proofs, initial on the left, the rest on the right. *)
  val proof_ids : int NTTyInitMap.t =
    let proof_id = ref 0 in
    let assign_id () =
      proof_id := !proof_id + 1;
      !proof_id
    in
    List.fold_left (fun acc proof ->
        NTTyInitMap.add (proof.derived, proof.initial) (assign_id ()) acc
      ) NTTyInitMap.empty proofs
  
  method string_of_nt_ty (hg : hgrammar) (nt, ty : nt_ty) : string =
    hg#nt_name nt ^ " : " ^ string_of_ty ty

  method string_of_edge (proof : proof) (edge : bool) : string =
    let sign =
      if edge then
        "+"
      else
        "-"
    in
    "== (" ^ string_of_int (NTTyInitMap.find (proof.derived, proof.initial) proof_ids) ^ ") " ^
    sign ^ " ==>"
  
  method string_of_paths (hg : hgrammar) : string =
    let proof_and_edge (proof, edge) =
      self#string_of_nt_ty hg proof.derived ^ "\n" ^
      self#string_of_edge proof edge
    in
    let escape_continuation =
      if NTTyMap.is_empty escape.nt_assumptions then
        ""
      else
        "\n=== (" ^
        string_of_int (NTTyInitMap.find (escape.derived, escape.initial) proof_ids) ^
        ") ===>\n" ^
        "..."
    in
    concat_map "\n" proof_and_edge path_to_cycle ^ "\n" ^
    "(CYCLE START)\n" ^
    concat_map "\n" proof_and_edge cycle ^ "\n" ^
    proof_and_edge (List.hd cycle) ^ "\n" ^
    "...\n" ^
    "(CYCLE END)\n" ^
    "===========>\n" ^
    self#string_of_nt_ty hg escape.derived ^
    escape_continuation
    
  method string_of_proofs (hg : hgrammar) : string =
    concat_map "\n\n" (fun proof ->
        string_of_proof hg (Some proof_ids) proof
      ) proofs
    
  method to_string (hg : hgrammar) : string =
    "A path in the Duplication Factor Graph proving infiniteness (the number is proof identifier, the sign is whether the edge is positive):\n\n" ^
    self#string_of_paths hg ^ "\n\n" ^
    "Proofs with identifiers (+ - positive duplication factor/multiple uses):\n\n" ^
    self#string_of_proofs hg

  method to_raw_edges : (nt_ty * bool) list =
    let cycle_border = fst @@ List.hd cycle in
    (List.map (fun (proof, edge_pos) -> (proof.derived, edge_pos)) @@
     path_to_cycle @ cycle) @
    [(cycle_border.derived, false)]
end
