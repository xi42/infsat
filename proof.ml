open Environment
open GrammarCommon
open HGrammar
open TargetEnvms
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

module HeadTyMap = Map.Make (struct
    type t = head * ty
    let compare = Utilities.compare_pair Pervasives.compare Ty.compare
  end)

(* note that var_assumptions is redundant, since it is included in derived *)
type proof = { derived : nt_ty;
               used_nts: used_nts;
               loc_types : loc_types;
               positive : bool;
               initial : bool}

let proof_compare (ignore_initial : bool) (proof1 : proof) (proof2 : proof) : int =
  compare_pair
    (compare_pair nt_ty_compare @@ NTTyMap.compare Pervasives.compare)
    Pervasives.compare
    ((proof1.derived, proof1.used_nts), (proof1.positive, proof1.initial || ignore_initial))
    ((proof2.derived, proof2.used_nts), (proof2.positive, proof2.initial || ignore_initial))
    
(** Information necessary to categorize given terminal or nonterminal as occuring everywhere with
    the same types or not. *)
type head_types = SingleLocCombination of int TyMap.t | MultiLocCombination

let string_of_proof (hg : hgrammar) (proof_ids : int NTTyInitMap.t option)
    (proof : proof) : string =
  let nt, ty = proof.derived in
  let hterm = hg#nt_body nt in
  (* info about proof number *)
  let proof_id_title =
    match proof_ids with
    | Some proof_ids ->
      let proof_id = NTTyInitMap.find (proof.derived, proof.initial) proof_ids in
      "(Proof " ^ string_of_int proof_id ^ ")\n"
    | None -> ""
  in
  let merge_loc_types (loc : hloc)
      (ty_counts : int TyMap.t) : head_types option -> head_types option =
    function
    | Some (SingleLocCombination existing_ty_counts) as single ->
      if TyMap.equal (fun count1 count2 -> count1 = count2 && count1 = 1)
          existing_ty_counts ty_counts then
        single
      else
        Some MultiLocCombination
    | Some MultiLocCombination as multi -> multi
    | None ->
      Some (SingleLocCombination ty_counts)
  in
  let loc2occ = hg#loc2head_occurence hterm in
  (* map from terminals/nonterminals to locations of their occurences and whether they should
     be marked, i.e., two locations have different sets of non-empty types or it is used multiple
     times in one location and there is another location where it has non-empty type *)
  let loc_combinations : head_types HeadMap.t =
    HeadMap.empty |>
    HlocMap.fold (fun loc ty_counts acc ->
        acc |> HeadMap.update (fst @@ HlocMap.find loc loc2occ) (merge_loc_types loc ty_counts)
      ) proof.loc_types
  in
  let multi_heads : HeadSet.t =
    HeadSet.of_seq @@
    Seq.map fst @@
    Seq.filter (fun (h, combinations) ->
        match combinations with
        | MultiLocCombination -> true
        | SingleLocCombination _ -> false
      ) @@
    HeadMap.to_seq loc_combinations
  in
  let loc2mark =
    loc2occ |>
    HlocMap.mapi (fun loc (h, occ) ->
        if HeadSet.mem h multi_heads then
          "#" ^ string_of_int (occ + 1)
        else
          ""
      )
  in
  let head_ty_locs : HlocSet.t HeadTyMap.t =
    HlocMap.bindings proof.loc_types |>
    List.fold_left (fun acc (loc, ty_counts) ->
        let head = fst @@ HlocMap.find loc loc2occ in
        TyMap.fold (fun ty _ acc ->
            acc |>
            HeadTyMap.update (head, ty) (function
                | Some locs -> Some (HlocSet.add loc locs)
                | None -> Some (HlocSet.singleton loc)
              )
          ) ty_counts acc
      ) HeadTyMap.empty
  in
  (* info which atom has which type *)
  let assumptions : string list =
    HeadTyMap.bindings head_ty_locs |>
    List.map (fun ((head, ty), locs) ->
        let prefix =
          match head with
          | HT a ->
            "(|-) "
          | HNT nt ->
            begin
              match proof_ids with
              | Some proof_ids ->
                (* There can still be two kinds of proofs - initial (first registered) and not.
                   Initial proofs can always point at initial proofs. Other proofs are proofs of
                   path to cycle and cycle itself, with all dependencies. So, the non-initial
                   proof may point at initial proof, but initial proof will never point at
                   non-initial proof unless it wasn't in the data. The dependency searched for
                   is with the same initial-ness, and, if it doesn't exist, with reverse
                   initial-ness. *)
                let proof_id =
                  match NTTyInitMap.find_opt ((nt, ty), proof.initial) proof_ids with
                  | Some proof_id' -> proof_id'
                  | None -> NTTyInitMap.find ((nt, ty), not proof.initial) proof_ids
                in
                "(" ^ string_of_int proof_id ^ ") "
              | None -> ""
            end
          | HVar v -> ""
        in
        let count_str_for_loc (loc : hloc) : string =
          let count : int = TyMap.find ty @@ HlocMap.find loc proof.loc_types in
          if count = 1 then
            ""
          else
            " (x" ^ string_of_int count ^ ")"
        in
        let heads_str : string =
          if HeadSet.mem head multi_heads then
            concat_map ", " (fun loc ->
                hg#string_of_head head ^ HlocMap.find loc loc2mark ^ count_str_for_loc loc
              ) @@ HlocSet.elements locs
          else
            (* it is guaranteed that either all locs have 1 or there is only one loc *)
            hg#string_of_head head ^ count_str_for_loc (HlocSet.choose locs)
        in
        prefix ^ heads_str ^ " : " ^ string_of_ty ty
      )
  in
  let annotated_hterm =
    hg#string_of_hterm false loc2mark 0 hterm
  in
  let positive_info =
    if proof.positive then
      " (+)"
    else
      ""
  in
  let nt_app =
    String.concat " " @@
    hg#nt_name nt :: hg#var_names nt
  in
  proof_id_title ^
  String.concat ",\n" assumptions ^
  "\n|- " ^ nt_app ^ " = " ^ annotated_hterm ^ " : " ^
  string_of_ty (codomain ty) ^ positive_info

(** Full information necessary to prove existence of a cycle and that the cycle is not omega. *)
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
  
  method string_of_paths (hg : hgrammar) : string =
    let prefix_empty = "    " in
    let prefix_mid = "|   " in
    let arrow_from_bottom = ".-> " in
    let string_of_edge (line_prefix : string) (proof : proof) (edge : bool) : string =
      let sign =
        if edge then
          "+"
        else
          "-"
      in
      let proof_id = NTTyInitMap.find (proof.derived, proof.initial) proof_ids in
      line_prefix ^ "    |\n" ^ line_prefix ^ "  (" ^ string_of_int proof_id ^ " " ^ sign ^ ") " ^
      "\n" ^ line_prefix ^ "    |\n" ^ line_prefix ^ "    v"
    in
    let string_of_last_edge (proof, edge : proof * bool) : string =
      let sign =
        if edge then
          "+"
        else
          "-"
      in
      let proof_id = NTTyInitMap.find (proof.derived, proof.initial) proof_ids in
      "|       |\n" ^
      "`---- (" ^ string_of_int proof_id ^ " " ^ sign ^ ")\n" ^
      "        |\n" ^
      "       ...\n" ^
      "        |\n" ^
      "        v"
    in
    let proof_and_edge first_line_prefix line_prefix (proof, edge) =
      first_line_prefix ^ self#string_of_nt_ty hg proof.derived ^ "\n" ^
      string_of_edge line_prefix proof edge
    in
    let path_to_cycle_strs =
      List.map (proof_and_edge prefix_empty prefix_empty) path_to_cycle
    in
    let cycle_len = List.length cycle in
    let cycle_head = List.hd cycle in
    let cycle_mid, cycle_last =
      if cycle_len > 1 then
        Utilities.split_list (cycle_len - 2) @@ List.tl cycle
      else
        ([], [])
    in
    let cycle_head_strs =
      if cycle_len > 1 then
        [proof_and_edge arrow_from_bottom prefix_mid cycle_head]
      else
        [
          arrow_from_bottom ^ self#string_of_nt_ty hg (fst cycle_head).derived;
          string_of_last_edge cycle_head
        ]
    in
    let cycle_mid_strs =
      List.map (proof_and_edge prefix_mid prefix_mid) cycle_mid
    in
    let cycle_last_strs =
      List.map (fun (proof, edge) ->
          prefix_mid ^ self#string_of_nt_ty hg proof.derived ^ "\n" ^
          string_of_last_edge (proof, edge)
        ) cycle_last
    in
    let escape_vertex =
      [prefix_empty ^ self#string_of_nt_ty hg escape.derived]
    in
    let escape_continuation =
      let continuation_str =
        if NTTyMap.is_empty escape.used_nts then
          " T"
        else
          "..."
      in
      let proof_id = NTTyInitMap.find (escape.derived, escape.initial) proof_ids in
      [
        prefix_empty ^ "    |";
        prefix_empty ^ "   (" ^ string_of_int proof_id ^ ")";
        prefix_empty ^ "    |";
        prefix_empty ^ "    v";
        prefix_empty ^ "   " ^ continuation_str
      ]
    in
    String.concat "\n" (
      path_to_cycle_strs @
      cycle_head_strs @
      cycle_mid_strs @
      cycle_last_strs @
      escape_vertex @
      escape_continuation
    )
    
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
