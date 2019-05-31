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

type loc_combinations = SingleLocCombination of int HlocMap.t | MultiLocCombination of HlocSet.t

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
  (* info which variable has which type *)
  let vars_info =
    array_listmap proof.var_assumptions (fun i ity ->
        [hg#var_name (nt, i) ^ " : " ^ string_of_ity ity]
      )
  in
  let merge_locs (locs : int HlocMap.t) : loc_combinations option -> loc_combinations option =
    function
    | Some (SingleLocCombination locs') as single ->
      if HlocMap.equal (=) locs' locs && locs |> HlocMap.for_all (fun _ count -> count = 1) then
        single
      else
        Some (MultiLocCombination (
            HlocSet.union (HlocMap.keys_set locs') (HlocMap.keys_set locs)))
    | Some (MultiLocCombination locs') ->
      Some (MultiLocCombination (
          HlocSet.union locs' (HlocMap.keys_set locs)))
    | None ->
      if locs |> HlocMap.for_all (fun _ count -> count = 1) || HlocMap.cardinal locs = 1 then
        Some (SingleLocCombination locs)
      else
        Some (MultiLocCombination (HlocMap.keys_set locs))
  in
  (* map from terminals/nonterminals to locations of their occurences and whether they should
     be marked, i.e., two locations have different sets of non-empty types or it is used multiple
     times in one location and there is another location where it has non-empty type *)
  let loc_combinations =
    HeadMap.empty |>
    NTTyMap.fold (fun (nt', _) locs acc ->
        acc |> HeadMap.update (HNT nt') (merge_locs locs)
      ) proof.nt_assumptions |> 
    TTyMap.fold (fun (a, _) locs acc ->
        acc |> HeadMap.update (HT a) (merge_locs locs)
      ) proof.t_assumptions
  in
  let multi_heads =
    HeadSet.of_seq @@
    Seq.map fst @@
    Seq.filter (fun (h, combinations) ->
        match combinations with
        | MultiLocCombination _ -> true
        | SingleLocCombination _ -> false
      ) @@
    HeadMap.to_seq loc_combinations
  in
  let loc2occ = hg#loc2head_occurence hterm in
  let loc2mark =
    loc2occ |>
    HlocMap.mapi (fun loc (h, occ) ->
        if HeadSet.mem h multi_heads then
          "#" ^ string_of_int (occ + 1)
        else
          ""
      )
  in
  let count_str_of_locs locs =
    (* it is guaranteed that either all locs have 1 or there is only one loc *)
    let count = snd @@ List.hd @@ HlocMap.bindings locs in
    if count > 1 then
      " (x" ^ string_of_int count ^ ")"
    else
      ""
  in
  let assumption_str h head_str ty locs =
    (* add occurence mark iff there is are 2+ locations of a nonterminal with non-empty
       and different different sets of types *)
    if HeadSet.mem h multi_heads then
      let marked =
        HlocMap.bindings locs |>
        List.map (fun (loc, count) ->
            let count_info =
              if count > 1 then
                " (x" ^ string_of_int count ^ ")"
              else
                ""
            in
            head_str ^ HlocMap.find loc loc2mark ^ count_info
          )
      in
      String.concat ", " marked ^ " : " ^ string_of_ty ty
    else
      head_str ^ count_str_of_locs locs ^ " : " ^ string_of_ty ty
  in
  let nts_info =
    NTTyMap.bindings proof.nt_assumptions |> List.map (fun ((nt', ty'), locs) ->
        let proof_id_str =
          match proof_ids with
          | Some proof_ids ->
            (* There can still be two kinds of proofs - initial (first registered) and not.
               Initial proofs can always point at initial proofs. Other proofs are proofs of
               path to cycle and cycle itself, with all dependencies. So, the non-initial
               proof may point at initial proof, but initial proof will never point at non-initial
               proof unless it wasn't in the data. The dependency searched for is with the
               same initial-ness, and, if it doesn't exist, with reverse initial-ness. *)
            let proof_id' =
              match NTTyInitMap.find_opt ((nt', ty'), proof.initial) proof_ids with
              | Some proof_id' -> proof_id'
              | None -> NTTyInitMap.find ((nt', ty'), not proof.initial) proof_ids
            in
            "(" ^ string_of_int proof_id' ^ ") "
          | None -> ""
        in
        [proof_id_str ^ assumption_str (HNT nt') (hg#nt_name nt') ty' locs]
      )
  in
  let ts_info =
    TTyMap.bindings proof.t_assumptions |> List.map (fun ((a, ty'), locs) ->
        ["(|-) " ^ assumption_str (HT a) (string_of_terminal a) ty' locs]
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
  String.concat ",\n" (List.concat @@ ts_info @ nts_info @ vars_info) ^
  "\n|- " ^ nt_app ^ " = " ^ annotated_hterm ^ " : " ^
  string_of_ty (codomain ty) ^ positive_info

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
        if NTTyMap.is_empty escape.nt_assumptions then
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
