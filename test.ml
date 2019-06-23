open Binding
open DuplicationFactorGraph
open Environment
open Grammar
open GrammarCommon
open HGrammar
open HtyStore
open Main
open OUnit2
open Proof
open TargetEnvms
open Type
open Typing
open TypingCommon
open Utilities

(* --- helper functions --- *)

let init_flags () =
  Flags.verbose_all := false;
  Flags.type_format := "short";
  Flags.force_unsafe := false;
  Flags.propagate_flags ()

let rec paths_equal path1 path2 =
  match path1, path2 with
  | (nt_ty1, true) :: path1', (nt_ty2, true) :: path2'
  | (nt_ty1, false) :: path1', (nt_ty2, false) :: path2' ->
    nt_ty_eq nt_ty1 nt_ty2 && paths_equal path1' path2'
  | [], [] -> true
  | _, _ -> false

let string_of_raw_path =
  string_of_list (fun (vertex, edge_pos) ->
      string_of_nt_ty vertex ^ " (" ^ string_of_int (int_of_bool edge_pos) ^ ")"
    )

let assert_equal_paths (expected : (dfg_vertex * bool) list) (cycle_proof : cycle_proof) =
  assert_equal ~printer:string_of_raw_path ~cmp:paths_equal
    expected
    (cycle_proof#to_raw_edges)

let assert_equal_envms envms1 envms2 =
  assert_equal ~printer:Envms.to_string ~cmp:Envms.equal
    (Envms.with_empty_temp_flags_and_locs envms1)
    (Envms.with_empty_temp_flags_and_locs envms2)

(** Asserts that two TEs are equal. Note that it uses default comparison, so it does not take
    into consideration that there are 3+ of a nonterminal or what terminals are used. *)
let assert_equal_tes te1 te2 =
  assert_equal ~printer:TargetEnvms.to_string ~cmp:TargetEnvms.equal
    (TargetEnvms.with_empty_temp_flags_and_locs te1)
    (TargetEnvms.with_empty_temp_flags_and_locs te2)

let mk_grammar rules =
  let nt_names = Array.mapi (fun i _ -> "N" ^ string_of_int i) rules in
  let g = new grammar nt_names [||] rules in
  print_verbose (not !Flags.quiet) @@ lazy (
    "Creating grammar:\n" ^ g#grammar_info ^ "\n"
  );
  EtaExpansion.eta_expand g;
  g

let mk_hgrammar g =
  new HGrammar.hgrammar g

let mk_cfa hg =
  let cfa = new Cfa.cfa hg in
  cfa#expand;
  cfa#compute_dependencies;
  cfa

let mk_typing g =
  let hg = mk_hgrammar g in
  (hg, new Typing.typing hg)

let type_check_nt_wo_env (typing : typing) (hg : hgrammar) (nt : nt_id) (target : ty) =
  typing#type_check (hg#nt_body nt) (Some target) (Right (hg#nt_arity nt))

let type_check_nt_wo_env_wo_target (typing : typing) (hg : hgrammar) (nt : nt_id) =
  typing#type_check (hg#nt_body nt) None (Right (hg#nt_arity nt))

let senv hg nt i ity_str =
  singleton_env (hg#nt_arity nt) (nt, i) @@ ity_of_string ity_str

let list_sort_eq (l1 : 'a list list) (l2 : 'a list list) : bool =
  (List.sort (compare_lists Pervasives.compare) l1) =
  (List.sort (compare_lists Pervasives.compare) l2)

let string_of_ll = string_of_list (string_of_list string_of_int)

(** Fake hterm location. *)
let l : int = 0

let mk_fake_envm (used_nts : used_nts) : bool -> env -> envm =
  mk_envm used_nts empty_loc_types

let assert_regexp_count (expected_count : int) (regexp : Str.regexp) (str : string) : unit =
  let rec count_aux i count =
    if i > String.length str then
      count
    else
      try
        let pos = Str.search_forward regexp str i in
        count_aux (pos + 1) (count + 1)
      with
      | Not_found -> count
  in
  assert_equal ~printer:string_of_int expected_count @@ count_aux 0 0

(* --- tests --- *)

let utilities_test () : test =
  "utilities" >::: [
    "range-0" >:: (fun _ ->
        assert_equal
          [0; 1; 2] @@
        range 0 3
      );

    "range-1" >:: (fun _ ->
        assert_equal
          [] @@
        range 1 1
      );
    
    "product-0" >:: (fun _ ->
        assert_equal ~cmp:list_sort_eq ~printer:string_of_ll
          [] @@
        product []
      );
    
    "product-1" >:: (fun _ ->
        assert_equal ~cmp:list_sort_eq ~printer:string_of_ll
          [[1]] @@
        product [[1]]
      );
    
    "product-2" >:: (fun _ ->
        assert_equal ~cmp:list_sort_eq ~printer:string_of_ll
          [[1; 2]] @@
        product [[1]; [2]]
      );
    
    "product-3" >:: (fun _ ->
        assert_equal ~cmp:list_sort_eq ~printer:string_of_ll
          [
            [1; 2; 3];
            [1; 2; 33];
            [1; 2; 333];
            [11; 2; 3];
            [11; 2; 33];
            [11; 2; 333]
          ] @@
        product [[1; 11]; [2]; [3; 33; 333]]
      );

    "product-4" >:: (fun _ ->
        assert_equal ~cmp:list_sort_eq ~printer:string_of_ll
          [
            [1; 2];
            [1; 22]
          ] @@
        product [[1]; [2; 22]]
      );

    "product-5" >:: (fun _ ->
        assert_equal ~cmp:list_sort_eq ~printer:string_of_ll
          [[1]; [2]] @@
        product [[1; 2]]
      );

    "flat_product-1" >:: (fun _ ->
        assert_equal ~cmp:list_sort_eq
          [] @@
        flat_product []
      );

    "flat_product-2" >:: (fun _ ->
        assert_equal ~cmp:list_sort_eq
          [] @@
        flat_product [[]]
      );

    "flat_product-3" >:: (fun _ ->
        assert_equal ~cmp:list_sort_eq
          [] @@
        flat_product [[]; []]
      );

    "flat_product-4" >:: (fun _ ->
        assert_equal ~cmp:list_sort_eq
          [
            [1; 2; 5];
            [1; 2; 6];
            [3; 4; 5];
            [3; 4; 6]
          ] @@
        flat_product [[[1; 2]; [3; 4]]; [[5]; [6]]]
      );
    
    "product_with_one_fixed-0" >:: (fun _ ->
        assert_equal ~cmp:list_sort_eq ~printer:string_of_ll
          [] @@
        product_with_one_fixed [] []
      );
    
    "product_with_one_fixed-1" >:: (fun _ ->
        assert_equal ~cmp:list_sort_eq ~printer:string_of_ll
          [[0]] @@
        product_with_one_fixed [[1; 2; 3]] [0]
      );
    
    "product_with_one_fixed-2" >:: (fun _ ->
        assert_equal ~cmp:list_sort_eq ~printer:string_of_ll
          [
            [0; 0];
            [0; 2];
            [0; 22];
            [1; 0];
            [11; 0]
          ] @@
        product_with_one_fixed [[1; 11]; [2; 22]] [0; 0]
      );
    
    "product_with_one_fixed-3" >:: (fun _ ->
        assert_equal ~cmp:list_sort_eq ~printer:string_of_ll
          [
            [0; 0; 0];
            [1; 0; 0];
            [0; 2; 0];
            [0; 0; 3];
            [0; 22; 0];
            [0; 222; 0];
            [1; 2; 0];
            [1; 0; 3];
            [1; 22; 0];
            [1; 222; 0];
            [0; 2; 3];
            [0; 22; 3];
            [0; 222; 3]
          ] @@
        product_with_one_fixed [[1]; [2; 22; 222]; [3]] [0; 0; 0]
      );
    
    "product_with_one_fixed-4" >:: (fun _ ->
        assert_equal ~cmp:list_sort_eq ~printer:string_of_ll
          [
            [0; 0; 0; 0];
            [1; 0; 0; 0];
            [0; 2; 0; 0];
            [0; 0; 3; 0];
            [0; 0; 0; 4];
            [1; 2; 0; 0];
            [1; 0; 3; 0];
            [1; 0; 0; 4];
            [0; 2; 3; 0];
            [0; 2; 0; 4];
            [0; 0; 3; 4];
            [0; 2; 3; 4];
            [1; 0; 3; 4];
            [1; 2; 0; 4];
            [1; 2; 3; 0]
          ] @@
        product_with_one_fixed [[1]; [2]; [3]; [4]] [0; 0; 0; 0]
      );
  ]

let mk_proof nt ty used_nts positive =
  { derived = (nt, ty);
    used_nts = used_nts;
    loc_types = empty_loc_types;
    positive = positive;
    initial = false
  }

let dfg_test () : test =
  "dfg" >::: [
    (* one node, no edges *)
    "dfg-0" >:: (fun _ ->
        assert_equal None @@
        (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_np empty_used_nts false;
          dfg
        )#find_positive_cycle 0 ty_np
      );

    (* unreachable loop *)
    "dfg-1" >:: (fun _ ->
        assert_equal None @@
        (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_np empty_used_nts false;
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_pr empty_used_nts true;
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_pr (nt_ty_used_once 0 ty_pr) true;
          dfg
        )#find_positive_cycle 0 ty_np
      );

    (* positive loop at start *)
    "dfg-2" >:: (fun _ ->
        assert_equal_paths
          [((0, ty_pr), true); ((0, ty_pr), false)] @@
        option_get @@ (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_pr empty_used_nts true;
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_pr (nt_ty_used_once 0 ty_pr) true;
          dfg
        )#find_positive_cycle 0 ty_pr
      );

    (* non-positive loop at start *)
    "dfg-3" >:: (fun _ ->
        assert_equal None @@
        (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_np empty_used_nts false;
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_np (nt_ty_used_once 0 ty_np) false;
          dfg
        )#find_positive_cycle 0 ty_np
      );

    (* non-positive and positive interconnected loops *)
    "dfg-4" >:: (fun _ ->
        assert_equal_paths
          [((0, ty_np), false); ((1, ty_np), true); ((2, ty_pr), false);
           ((3, ty_np), false); ((1, ty_np), false)] @@
        option_get @@ (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex @@ mk_proof 3 ty_np empty_used_nts false;
          ignore @@ dfg#add_vertex @@ mk_proof 2 ty_pr (nt_ty_used_once 3 ty_np) false;
          ignore @@ dfg#add_vertex @@ mk_proof 1 ty_np (nt_ty_used_once 2 ty_pr) true;
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_np (nt_ty_used_once 1 ty_np) false;
          ignore @@ dfg#add_vertex @@ mk_proof 4 ty_np (nt_ty_used_once 3 ty_np) false;
          ignore @@ dfg#add_vertex @@ mk_proof 1 ty_np (nt_ty_used_once 4 ty_np) false;
          ignore @@ dfg#add_vertex @@ mk_proof 3 ty_np (nt_ty_used_once 1 ty_np) false;
          dfg
        )#find_positive_cycle 0 ty_np
      );

    (* non-positive and positive interconnected loops - another order *)
    "dfg-5" >:: (fun _ ->
        assert_equal_paths
          [((0, ty_np), false); ((1, ty_np), true); ((4, ty_np), false);
           ((3, ty_np), false); ((1, ty_np), false)] @@
        option_get @@ (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex @@ mk_proof 3 ty_np empty_used_nts false;
          ignore @@ dfg#add_vertex @@ mk_proof 2 ty_pr (nt_ty_used_once 3 ty_np) false;
          ignore @@ dfg#add_vertex @@ mk_proof 1 ty_np (nt_ty_used_once 2 ty_pr) false;
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_np (nt_ty_used_once 1 ty_np) false;
          ignore @@ dfg#add_vertex @@ mk_proof 4 ty_np (nt_ty_used_once 3 ty_np) false;
          ignore @@ dfg#add_vertex @@ mk_proof 1 ty_np (nt_ty_used_once 4 ty_np) true;
          ignore @@ dfg#add_vertex @@ mk_proof 3 ty_np (nt_ty_used_once 1 ty_np) false;
          dfg
        )#find_positive_cycle 0 ty_np
      );

    (* non-positive loop and positive path *)
    "dfg-6" >:: (fun _ ->
        assert_equal None @@
        (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex @@ mk_proof 1 ty_np empty_used_nts false;
          ignore @@ dfg#add_vertex @@ mk_proof 5 ty_np (nt_ty_used_once 1 ty_np) false;
          ignore @@ dfg#add_vertex @@ mk_proof 4 ty_np (nt_ty_used_once 5 ty_np) false;
          ignore @@ dfg#add_vertex @@ mk_proof 1 ty_np (nt_ty_used_once 4 ty_np) false;
          ignore @@ dfg#add_vertex @@ mk_proof 3 ty_np empty_used_nts false;
          ignore @@ dfg#add_vertex @@ mk_proof 2 ty_pr (nt_ty_used_once 3 ty_np) false;
          ignore @@ dfg#add_vertex @@ mk_proof 1 ty_np (nt_ty_used_once 2 ty_pr) true;
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_np (nt_ty_used_once 1 ty_np) false;
          dfg
        )#find_positive_cycle 0 ty_np
      );

    (* registering twice the same vertex *)
    "dfg-7" >:: (fun _ ->
        assert_equal_paths
          [((0, ty_pr), true); ((0, ty_pr), false)] @@
        option_get @@ (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_pr empty_used_nts true;
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_pr (nt_ty_used_once 0 ty_pr) true;
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_pr (nt_ty_used_once 0 ty_pr) false;
          dfg
        )#find_positive_cycle 0 ty_pr
      );

    (* checking for not registered vertex *)
    "dfg-8" >:: (fun _ ->
        assert_equal None @@
        (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_pr empty_used_nts true;
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_pr (nt_ty_used_once 0 ty_pr) true;
          dfg
        )#find_positive_cycle 0 ty_np
      );

    (* cycle at start, but not on the same vertex *)
    "dfg-9" >:: (fun _ ->
        assert_equal_paths
          [((0, ty_pr), true); ((1, ty_pr), true); ((0, ty_pr), false)] @@
        option_get @@ (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex @@ mk_proof 1 ty_pr empty_used_nts true;
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_pr (nt_ty_used_once 1 ty_pr) true;
          ignore @@ dfg#add_vertex @@ mk_proof 1 ty_pr (nt_ty_used_once 0 ty_pr) true;
          dfg
        )#find_positive_cycle 0 ty_pr
      );

    (* two cycles, one shorter, the shorter one should be selected *)
    "dfg-10" >:: (fun _ ->
        assert_equal_paths
          [((0, ty_pr), false); ((4, ty_pr), false); ((3, ty_pr), true); ((0, ty_pr), false)] @@
        option_get @@ (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_pr empty_used_nts false;
          ignore @@ dfg#add_vertex @@ mk_proof 3 ty_pr (nt_ty_used_once 0 ty_pr) true;
          ignore @@ dfg#add_vertex @@ mk_proof 2 ty_pr (nt_ty_used_once 3 ty_pr) false;
          ignore @@ dfg#add_vertex @@ mk_proof 1 ty_pr (nt_ty_used_once 2 ty_pr) false;
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_pr (nt_ty_used_once 1 ty_pr) false;
          ignore @@ dfg#add_vertex @@ mk_proof 4 ty_pr (nt_ty_used_once 3 ty_pr) false;
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_pr (nt_ty_used_once 4 ty_pr) false;
          dfg
        )#find_positive_cycle 0 ty_pr
      );

    (* two cycles, one shorter - another order, the shorter one should be selected *)
    "dfg-11" >:: (fun _ ->
        assert_equal_paths
          [((0, ty_pr), false); ((1, ty_pr), false); ((2, ty_pr), true); ((0, ty_pr), false)] @@
        option_get @@ (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_pr empty_used_nts false;
          ignore @@ dfg#add_vertex @@ mk_proof 2 ty_pr (nt_ty_used_once 0 ty_pr) true;
          ignore @@ dfg#add_vertex @@ mk_proof 1 ty_pr (nt_ty_used_once 2 ty_pr) false;
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_pr (nt_ty_used_once 1 ty_pr) false;
          ignore @@ dfg#add_vertex @@ mk_proof 4 ty_pr (nt_ty_used_once 2 ty_pr) false;
          ignore @@ dfg#add_vertex @@ mk_proof 3 ty_pr (nt_ty_used_once 4 ty_pr) false;
          ignore @@ dfg#add_vertex @@ mk_proof 0 ty_pr (nt_ty_used_once 3 ty_pr) false;
          dfg
        )#find_positive_cycle 0 ty_pr
      );

    (* add_vertex should return whether new edge was added, checking other data *)
    "dfg-12" >:: (fun _ ->
        let proof1 = mk_proof 0 ty_np empty_used_nts false in
        let proof2 = mk_proof 0 ty_pr (nt_ty_used_once 0 ty_np) true in
        let proof3 = mk_proof 0 ty_pr (nt_ty_used_once 0 ty_np) false in
        let proof4 = mk_proof 0 ty_pr (nt_ty_used_once 0 ty_pr) true in
        let dfg = new dfg in
        assert_equal None @@ dfg#find_positive_cycle 0 ty_pr;
        (* note that no edge is added, only vertex, so expecting false *)
        assert_equal false @@ dfg#add_vertex proof1;
        assert_equal None @@ dfg#find_positive_cycle 0 ty_pr;
        assert_equal true @@ dfg#add_vertex proof3;
        (* edge should be replaced with positive one *)
        assert_equal true @@ dfg#add_vertex proof2;
        assert_equal None @@ dfg#find_positive_cycle 0 ty_pr;
        (* these edges should be ignored as there is already a positive edge present there *)
        assert_equal false @@ dfg#add_vertex proof2;
        assert_equal false @@ dfg#add_vertex proof3;
        assert_equal None @@ dfg#find_positive_cycle 0 ty_pr;
        assert_equal true @@ dfg#add_vertex proof4;
        let cycle = option_get @@ dfg#find_positive_cycle 0 ty_pr in
        let path_to_cycle, cycle, escape, proofs = cycle#raw_data in
        assert_equal 0 @@ List.length path_to_cycle;
        assert_equal 1 @@ List.length cycle;
        assert_equal proof4 @@ fst @@ List.hd cycle;
        (* no need to define custom equality, since dfg modifies only initial flag *)
        assert_equal {proof3 with initial = true} escape;
        assert_equal 3 @@ List.length proofs
      );

    (* checking a border case where initial proof tree crosses path to cycle - this is another
       case aside from escape vertex where the same vertex can be included in list of proofs
       twice. *)
    "dfg-13" >:: (fun _ ->
        let dfg = new dfg in
        (* 10, 11 <- 9 <- 2 *)
        ignore @@ dfg#add_vertex @@ mk_proof 10 ty_np empty_used_nts false;
        ignore @@ dfg#add_vertex @@ mk_proof 11 ty_np empty_used_nts false;
        ignore @@ dfg#add_vertex @@ mk_proof 9 ty_pr
          (NTTyMap.of_seq @@ List.to_seq [((10, ty_np), false); ((11, ty_np), false)]) true;
        ignore @@ dfg#add_vertex @@ mk_proof 2 ty_pr
          (NTTyMap.of_seq @@ List.to_seq [((9, ty_pr), false)]) false;
        (* 8, 2 <- 5 *)
        ignore @@ dfg#add_vertex @@ mk_proof 8 ty_np empty_used_nts false;
        ignore @@ dfg#add_vertex @@ mk_proof 5 ty_pr
          (NTTyMap.of_seq @@ List.to_seq [((2, ty_pr), false); ((8, ty_np), false)]) false;
        (* 5 <- 7 *)
        ignore @@ dfg#add_vertex @@ mk_proof 7 ty_pr
          (NTTyMap.of_seq @@ List.to_seq [((5, ty_pr), false)]) false;
        (* 8 <- 6 *)
        ignore @@ dfg#add_vertex @@ mk_proof 6 ty_pr
          (NTTyMap.of_seq @@ List.to_seq [((8, ty_np), true)]) true;
        (* cycle: 5 : pr, 6 : pr <- 4 : pr; 4 : pr, 6 : pr <- 5 : pr *)
        ignore @@ dfg#add_vertex @@ mk_proof 4 ty_pr
          (NTTyMap.of_seq @@ List.to_seq [((5, ty_pr), false); ((6, ty_pr), false)]) false;
        ignore @@ dfg#add_vertex @@ mk_proof 5 ty_pr
          (NTTyMap.of_seq @@ List.to_seq [((4, ty_pr), false); ((6, ty_pr), false)]) false;
        (* 7 <- 4 - this should be ignored *)
        ignore @@ dfg#add_vertex @@ mk_proof 4 ty_pr
          (NTTyMap.of_seq @@ List.to_seq [((7, ty_pr), false)]) false;
        (* 4 <- 3 <- 2 <- 1 <- 0 *)
        ignore @@ dfg#add_vertex @@ mk_proof 3 ty_pr
          (NTTyMap.of_seq @@ List.to_seq [((4, ty_pr), false)]) false;
        ignore @@ dfg#add_vertex @@ mk_proof 2 ty_pr
          (NTTyMap.of_seq @@ List.to_seq [((3, ty_pr), false)]) false;
        ignore @@ dfg#add_vertex @@ mk_proof 1 ty_pr
          (NTTyMap.of_seq @@ List.to_seq [((2, ty_pr), false)]) false;
        ignore @@ dfg#add_vertex @@ mk_proof 0 ty_pr
          (NTTyMap.of_seq @@ List.to_seq [((1, ty_pr), false)]) false;
        (* 0 -> 1 -> 2 -> 3 -> [4 -> 5 -> ...] -> 5 -> 8, 2 -> 9 -> 10, 11
           Note that 4 -> 7 -> 5 branch should be ignored, as it should not be found as start of
           escape path, since it goes back to the cycle.
           Additionally, 9, 10, 11 should not be forgotten just because 2 -> 1, since 2 -> 1
           is not an initial proof.
           We have proofs of 0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, again 2 and again 5 *)
        let cycle = option_get @@ dfg#find_positive_cycle 0 ty_pr in
        let path_to_cycle, cycle, escape, proofs = cycle#raw_data in
        (* checking cycle *)
        assert_equal ~printer:(Utilities.string_of_list string_of_int)
          [4; 5] @@
        List.sort Pervasives.compare @@ List.map (fun n -> let p = fst n in fst p.derived)
          cycle;
        (* checking path to cycle *)
        assert_equal ~printer:(Utilities.string_of_list string_of_int)
          [0; 1; 2; 3] @@
        List.sort Pervasives.compare @@ List.map (fun n -> let p = fst n in fst p.derived)
          path_to_cycle;
        assert_equal ~printer:string_of_int 5 @@ fst @@ escape.derived;
        (* checking that all required proofs and only required proofs (i.e., except 7) are
           present *)
        assert_equal ~printer:(Utilities.string_of_list string_of_int)
          [0; 1; 2; 2; 3; 4; 5; 5; 6; 8; 9; 10; 11] @@
        List.sort Pervasives.compare @@ List.map (fun p -> fst @@ p.derived) proofs
      );
  ]

let conversion_test () : test =
  (* These preterminals are defined in a way so that they should be converted to respective
     terminals from paper without creating additional terms (such as functions). *)
  let preserved_preterminals = [
    Syntax.Terminal ("a_", 1, true, false);
    Syntax.Terminal ("b_", 2, false, false);
    Syntax.Terminal ("e_", 0, false, false);
    Syntax.Terminal ("t_", 2, false, true);
    Syntax.Terminal ("id", 1, false, false)
  ] in
  (* This grammar is used to test all combinations of applications of custom terminals
     identical to a, b, e, t with all possible numbers of applied arguments.
     It also tests that not counted terminal with one child is removed when it has an
     argument (as it is identity). *)
  let test_terminals_prerules = [
    ("E", [], Syntax.PApp (Syntax.Name "e_", []));
    ("A", ["x"], Syntax.PApp (Syntax.Name "a_", [
         Syntax.PApp (Syntax.Name "x", [])
       ]));
    ("B", [], Syntax.PApp (Syntax.Name "b_", []));
    ("Be", [], Syntax.PApp (Syntax.Name "b_", [
         Syntax.PApp (Syntax.Name "e_", [])
       ]));
    ("BAee", [], Syntax.PApp (Syntax.Name "b_", [
         Syntax.PApp (Syntax.Name "a_", [Syntax.PApp (Syntax.Name "e_", [])]);
         Syntax.PApp (Syntax.Name "e_", [])
       ]));
    ("X", ["x"], Syntax.PApp (Syntax.Name "x", [
         Syntax.PApp (Syntax.Name "e_", [])
       ]));
    ("Xa", [], Syntax.PApp (Syntax.NT "X", [
         Syntax.PApp (Syntax.Name "a_", [])
       ]));
    ("IDe", [], Syntax.PApp (Syntax.Name "id", [
         Syntax.PApp (Syntax.Name "e_", [])
       ]));
    ("ID", [], Syntax.PApp (Syntax.Name "id", []));
    ("BR", [], Syntax.PApp (Syntax.Name "b_", []));
    ("BRe", [], Syntax.PApp (Syntax.Name "b_", [
         Syntax.PApp (Syntax.Name "e_", [])
       ]));
    ("TRee", [], Syntax.PApp (Syntax.Name "t_", [
         Syntax.PApp (Syntax.Name "e_", []);
         Syntax.PApp (Syntax.Name "e_", [])
       ]));
    ("BRxy", ["x"; "y"], Syntax.PApp (Syntax.Name "b_", [
         Syntax.PApp (Syntax.Name "x", []);
         Syntax.PApp (Syntax.Name "y", [])
       ]))
  ] in
  let t_gram = Conversion.prerules2gram (test_terminals_prerules, preserved_preterminals) in
  print_verbose !Flags.verbose_preprocessing @@ lazy (
    "Basic-like terminals test grammar:\n" ^ t_gram#grammar_info ^ "\n"
  );
  (* This grammar is used to test function conversion. *)
  let f_prerules = [
    ("E", [], Syntax.PApp (Syntax.Name "e", []));
    ("F", ["x"; "y"], Syntax.PApp (
        Syntax.Fun (["p"; "q"], Syntax.PApp (Syntax.Name "p", [
            Syntax.PApp (Syntax.Name "y", [])
          ])),
        [
          Syntax.PApp (Syntax.Name "x", [])
        ]))
  ] in
  let f_gram = Conversion.prerules2gram (f_prerules, []) in
  print_verbose !Flags.verbose_preprocessing @@ lazy (
    "Fun test grammar:\n" ^ t_gram#grammar_info ^ "\n"
  );
  (* This grammar is used to test custom terminals that are not preserved as one of default
     terminals. *)
  let c_preterminals = [
    Syntax.Terminal ("attt", 3, true, true);
    Syntax.Terminal ("ttt", 3, false, true);
    Syntax.Terminal ("bbbb", 4, false, false);
    Syntax.Terminal ("ae", 0, true, true);
    Syntax.Terminal ("auniv", 1, true, true);
  ] in
  let c_prerules = [
    ("ATTT", [], Syntax.PApp (Syntax.Name "attt", []));
    ("TTT", [], Syntax.PApp (Syntax.Name "ttt", []));
    ("BBBB", [], Syntax.PApp (Syntax.Name "bbbb", []));
    ("AE", [], Syntax.PApp (Syntax.Name "ae", []));
    ("AU", [], Syntax.PApp (Syntax.Name "auniv", []))
  ] in
  let c_gram = Conversion.prerules2gram (c_prerules, c_preterminals) in
  print_verbose !Flags.verbose_preprocessing @@ lazy (
    "Custom terminals test grammar:\n" ^ c_gram#grammar_info ^ "\n"
  );
  (* This grammar is used to test function variable scopes. *)
  let s_prerules = [
    (* F -> (fun x -> fun x -> fun x -> x) e e e *)
    ("F", [], Syntax.PApp (
        Syntax.Fun (["x"], Syntax.PApp (
            Syntax.Fun (["x"], Syntax.PApp (
                Syntax.Fun (["x"], Syntax.PApp (
                    Syntax.Name "x", []
                  )),
                [])),
            [])),
        [Syntax.PApp (Syntax.Name "e", []);
         Syntax.PApp (Syntax.Name "e", []);
         Syntax.PApp (Syntax.Name "e", [])]
      ))
  ] in
  let s_gram = Conversion.prerules2gram (s_prerules, []) in
  print_verbose !Flags.verbose_preprocessing @@ lazy (
    "Function scope test grammar:\n" ^ s_gram#grammar_info ^ "\n"
  );
  "conversion" >::: [
    (* Terminals a, b, e, t should be preserved without needless conversion. Therefore, there
       should be no functions apart from the one from identity without arguments, i.e.,
       exactly one extra rule. *)
    "prerules2gram-t1" >:: (fun _ ->
        assert_equal ~printer:string_of_int 14 @@
        Array.length t_gram#rules
      );

    (* Checking that number of leaf terms is correct - nothing extra was added or removed
       aside from extra rule from identity without arguments. *)
    "prerules2gram-t2" >:: (fun _ ->
        assert_equal ~printer:string_of_int 26
        t_gram#size
      );

    "prerules2gram-t3" >:: (fun _ ->
        assert_equal (TE T) @@
        term_head @@ snd @@ t_gram#rules.(t_gram#nt_with_name "TRee")
      );

    "prerules2gram-t4" >:: (fun _ ->
        assert_equal (TE B) @@
        term_head @@ snd @@ t_gram#rules.(t_gram#nt_with_name "BRxy")
      );

    "prerules2gram-t5" >:: (fun _ ->
        assert_equal (NT (t_gram#nt_count - 1)) @@
        term_head @@ snd @@ t_gram#rules.(t_gram#nt_with_name "ID")
      );

    (* Testing that only used part of closure and all variables are in arguments *)
    "prerules2gram-f1" >:: (fun _ ->
        let f_nt : nt_id = f_gram#nt_count - 1 in
        let arity = fst @@ f_gram#rules.(f_nt) in
        assert_equal ["y"; "p"; "q"] @@
        List.map (fun i -> f_gram#name_of_var (f_nt, i)) @@ range 0 arity
      );

    (* Checking that fun application was converted to _fun0 y x. *)
    "prerules2gram-f2" >:: (fun _ ->
        let f_nt : nt_id = f_gram#nt_count - 1 in
        assert_equal (2, App (
            App (
              NT f_nt,
              Var (f_gram#nt_with_name "F", 1)
            ),
            Var (f_gram#nt_with_name "F", 0)
          )) @@
        f_gram#rules.(f_gram#nt_with_name "F")
      );

    "prerules2gram-c1" >:: (fun _ ->
        assert_equal ~printer:string_of_int 8 @@
        Array.length c_gram#rules
      );

    "prerules2gram-c2" >:: (fun _ ->
        match c_gram#rules.(c_gram#nt_with_name "ATTT") with
        | 0, NT nt ->
          let rule = c_gram#rules.(nt) in
          assert_equal (3, 6, TE A) @@
          (fst @@ rule, size_of_rule rule, term_head @@ snd rule)
        | _, _ -> assert_failure "wrong conversion"
      );

    "prerules2gram-c3" >:: (fun _ ->
        match c_gram#rules.(c_gram#nt_with_name "TTT") with
        | 0, NT nt ->
          let rule = c_gram#rules.(nt) in
          assert_equal (3, 5, TE T) @@
          (fst @@ rule, size_of_rule rule, term_head @@ snd rule)
        | _, _ -> assert_failure "wrong conversion"
      );

    "prerules2gram-c4" >:: (fun _ ->
        match c_gram#rules.(c_gram#nt_with_name "BBBB") with
        | 0, NT nt ->
          let rule = c_gram#rules.(nt) in
          assert_equal (4, 7, TE B) @@
          (fst @@ rule, size_of_rule rule, term_head @@ snd rule)
        | _, _ -> assert_failure "wrong conversion"
      );

    "prerules2gram-c5" >:: (fun _ ->
        assert_equal (0, App (TE A, TE E)) @@
        c_gram#rules.(c_gram#nt_with_name "AE")
      );

    "prerules2gram-c6" >:: (fun _ ->
        assert_equal (0, TE A) @@
        c_gram#rules.(c_gram#nt_with_name "AU")
      );

    (* Three nested functions convert to three new nonterminals. *)
    "prerules2gram-s1" >:: (fun _ ->
        assert_equal ~printer:string_of_int 4 @@
        Array.length s_gram#rules
      );

    (* Since each function shadows x from closure, none of them should take a variable from
       closure into nonterminal definition. *)
    "prerules2gram-s2" >:: (fun _ ->
        assert_equal [0; 1; 1; 1] @@
        List.map fst @@ Array.to_list s_gram#rules
      );

    (* Inner function should use its own x. *)
    "prerules2gram-s3" >:: (fun _ ->
        assert_equal (Var (3, 0)) @@
        snd @@ s_gram#rules.(3)
      );
  ]

let type_test () : test =
  "type" >::: [
    "string_of_ty-1" >:: (fun _ ->
        assert_equal ~printer:id "pr" @@ string_of_ty ty_pr
      );

    "string_of_ty-2" >:: (fun _ ->
        assert_equal ~printer:id "np -> pr" @@
        string_of_ty @@ mk_fun [ity_np] true
      );

    "string_of_ty-3" >:: (fun _ ->
        assert_equal ~printer:id "(np -> pr) -> np" @@
        string_of_ty @@ mk_fun [sty (mk_fun [ity_np] true)] false
      );

    "string_of_ty-4" >:: (fun _ ->
        assert_equal ~printer:id "np /\\ pr -> pr" @@
        string_of_ty @@ mk_fun [TyList.of_list [ty_pr; ty_np]] true
      );

    "string_of_ty-5" >:: (fun _ ->
        assert_equal ~printer:id "T -> pr" @@
        string_of_ty @@ mk_fun [ity_top] true
      );

    "string_of_ty-6" >:: (fun _ ->
        assert_equal ~printer:id "(pr -> pr) -> (np -> pr) -> np -> pr" @@
        string_of_ty @@
        mk_fun [sty @@ mk_fun [ity_pr] true; sty @@ mk_fun [ity_np] true; ity_np] true
      );

    "string_of_ity-1" >:: (fun _ ->
        assert_equal ~printer:id "(pr -> pr) /\\ (np -> np)" @@
        string_of_ity (TyList.of_list [mk_fun [ity_pr] true; mk_fun [ity_np] false])
      );
    
    "ty_of_string-1" >:: (fun _ ->
        assert_equal ~cmp:Ty.equal ty_pr @@ ty_of_string "pr"
      );

    "ty_of_string-2" >:: (fun _ ->
        assert_equal ~cmp:Ty.equal (mk_fun [ity_np] true) @@ ty_of_string "np -> pr"
      );

    "ty_of_string-3" >:: (fun _ ->
        assert_equal ~cmp:Ty.equal (mk_fun [sty @@ mk_fun [ity_np] true] false) @@
        ty_of_string "(np -> pr) -> np"
      );

    "ty_of_string-4" >:: (fun _ ->
        assert_equal ~cmp:Ty.equal (mk_fun [TyList.of_list [ty_np; ty_pr]] true) @@
        ty_of_string "pr /\\ np -> pr"
      );

    "ty_of_string-5" >:: (fun _ ->
        assert_equal ~cmp:Ty.equal (mk_fun [ity_top] true) @@
        ty_of_string "T -> pr"
      );

    "ty_of_string-6" >:: (fun _ ->
        assert_equal ~cmp:Ty.equal
          (mk_fun [sty @@ mk_fun [ity_pr] true; sty @@ mk_fun [ity_np] true; ity_np] true) @@
        ty_of_string "(pr -> pr) -> (np -> pr) -> np -> pr"
      );

    "ity_of_string-1" >:: (fun _ ->
        assert_equal ~cmp:TyList.equal
          (TyList.of_list [mk_fun [ity_pr] true; mk_fun [ity_np] false]) @@
        ity_of_string "(pr -> pr) /\\ (np -> np)"
      );
  ]

let te_test () : test =
  "targetEnvms" >::: [
    "intersect-1" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.singleton_empty_meta ty_np @@ empty_env 0) @@
        TargetEnvms.intersect
          (TargetEnvms.singleton_empty_meta ty_np @@ empty_env 0)
          (TargetEnvms.singleton_empty_meta ty_np @@ empty_env 0)
      );

    "intersect-2" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list [
              (ty_np, [with_positive true @@ with_dup true @@
                    mk_envm_empty_meta @@ singleton_env 1 (0, 0) @@ sty ty_pr])
            ]) @@
        TargetEnvms.intersect
          (TargetEnvms.of_list_empty_flags_empty_meta [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_pr])
            ])
          (TargetEnvms.of_list_empty_flags_empty_meta [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_pr])
            ])
      );

    "intersect-3" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list_empty_flags_empty_meta [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np])
            ]) @@
        TargetEnvms.intersect
          (TargetEnvms.of_list_empty_flags_empty_meta [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np])
            ])
          (TargetEnvms.of_list_empty_flags_empty_meta [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np])
            ])
      );

    "intersect-4" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_envm
                         (NTTyMap.of_list [
                             ((0, ty_pr), false);
                             ((0, ty_np), false)
                           ])
                         empty_loc_types true])
            ]) @@
        TargetEnvms.intersect
          (TargetEnvms.of_list [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_envm
                         (nt_ty_used_once 0 ty_pr) empty_loc_types true])
            ])
          (TargetEnvms.of_list [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_envm
                         (nt_ty_used_once 0 ty_np) empty_loc_types true;
                       singleton_env 1 (0, 0) @@ sty ty_np |> mk_envm
                         (nt_ty_used_once 0 ty_np) empty_loc_types false]);
              (ty_pr, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_envm
                         empty_used_nts empty_loc_types false])
            ])
      );

    "intersect-5" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_fake_envm
                      (NTTyMap.of_list [((0, ty_np), true)]) false;
                    singleton_env 1 (0, 0) @@ sty ty_np |> mk_fake_envm
                      (NTTyMap.of_list [((0, ty_np), true)]) true]);
            ]) @@
        TargetEnvms.intersect
          (TargetEnvms.of_list [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_fake_envm
                         (nt_ty_used_once 0 ty_np) false])
            ])
          (TargetEnvms.of_list [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_fake_envm
                         (nt_ty_used_once 0 ty_np) true]);
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_fake_envm
                         (nt_ty_used_once 0 ty_np) false]);
              (ty_pr, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_fake_envm
                         empty_used_nts false])
            ])
      );

    "intersect-6" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list_empty_flags_empty_meta [
              (ty_np, [singleton_env 2 (0, 0) @@ ity_of_string "pr /\\ np";
                    singleton_env 2 (0, 1) @@ ity_of_string "pr /\\ np";
                    new env [|sty ty_np; sty ty_pr|];
                    new env [|sty ty_pr; sty ty_np|]
                   ]);
            ]) @@
        TargetEnvms.intersect
          (TargetEnvms.of_list_empty_flags_empty_meta [
              (ty_np, [singleton_env 2 (0, 0) @@ sty ty_np]);
              (ty_np, [singleton_env 2 (0, 1) @@ sty ty_np])
            ])
          (TargetEnvms.of_list_empty_flags_empty_meta [
              (ty_np, [singleton_env 2 (0, 0) @@ sty ty_pr]);
              (ty_np, [singleton_env 2 (0, 1) @@ sty ty_pr])
            ])
      );

    "size-1" >:: (fun _ ->
        assert_equal ~printer:string_of_int 1 @@
        TargetEnvms.size @@
        TargetEnvms.singleton_empty_meta ty_np @@
        singleton_env 3 (0, 2) @@ sty ty_np
      );
  ]

(** The smallest possible grammar. *)
let grammar_e () = mk_grammar
    [|
      (0, TE E) (* N0 -> e *)
    |]

let typing_e_test () =
  let hg, typing = mk_typing @@ grammar_e () in
  [
    (* check if e : np type checks *)
    "type_check-1" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.singleton_empty_meta ty_np @@ empty_env @@ hg#nt_arity 0)
          (type_check_nt_wo_env typing hg 0 ty_np false false l)
      );

    (* checking basic functionality of forcing pr vars *)
    "type_check-2" >:: (fun _ ->
        assert_equal_tes
          TargetEnvms.empty
          (type_check_nt_wo_env typing hg 0 ty_np false true l)
      );

    (* checking that forcing no pr vars does not break anything when there are only terminals *)
    "type_check-3" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.singleton_empty_meta ty_np @@ empty_env @@ hg#nt_arity 0)
          (type_check_nt_wo_env typing hg 0 ty_np true false l)
      );
  ]

(** Grammar that tests usage of a variable. *)
let grammar_ax () = mk_grammar
    [|
      (0, App (NT 1, TE E)); (* N0 -> N1 e *)
      (1, App (TE A, Var (1, 0))) (* N1 x -> a x *)
    |]

let typing_ax_test () =
  let hg, typing = mk_typing @@ grammar_ax () in
  [
    (* check that a x : pr accepts both productivities of x *)
    "type_check-4" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list
           [
             (ty_pr, [
                 mk_fake_envm empty_used_nts true @@ senv hg 1 0 "pr";
                 mk_fake_envm empty_used_nts true @@ senv hg 1 0 "np"
              ])
           ])
          (type_check_nt_wo_env typing hg 1 ty_pr false false l)
      );

    (* check that a x : np does not type check *)
    "type_check-5" >:: (fun _ ->
        assert_equal_tes
          TargetEnvms.empty
          (type_check_nt_wo_env typing hg 1 ty_np false false l)
      );
  ]
  
(** Grammar that tests intersection - x and y are inferred from one argument in N1 rule, and y and
    z from the other. N4 tests top. *)
let grammar_xyyz () = mk_grammar
    [|
      (* N0 -> N1 a N4 e *)
      (0, App (App (App (NT 1, TE A), NT 4), TE E));
      (* N1 x y z -> N2 x y (N3 y z) *)
      (3, App (
          App (App (NT 2, Var (1, 0)), Var (1, 1)),
          App (App (NT 3, Var (1, 1)), Var (1, 2))
        ));
      (* N2 x y v -> x (y v) *)
      (3, App (Var (2, 0), App (Var (2, 1), Var (2, 2))));
      (* N3 y z -> y z *)
      (2, App (Var (3, 0), Var (3, 1)));
      (* N4 x -> b (a x) x *)
      (1, App (App (TE B, App (TE A, Var (4, 0))), Var (4, 0)));
      (* N5 -> N5 *)
      (0, NT 5)
    |]

let typing_xyyz_test () =
  let hg, typing = mk_typing @@ grammar_xyyz () in
  ignore @@ typing#add_nt_ty 2 @@ ty_of_string "(pr -> pr) -> (np -> pr) -> np -> pr";
  ignore @@ typing#add_nt_ty 3 @@ ty_of_string "(np -> np) -> np -> np";
  let id0_0 = hg#locate_hterms_id 0 [0] in
  ignore @@ typing#get_hty_store#add_hty id0_0
    [
      ity_of_string "pr -> pr";
      ity_of_string "np -> np";
      ity_of_string "np -> pr"
    ];
  ignore @@ typing#get_hty_store#add_hty id0_0
    [
      ity_of_string "pr -> pr";
      ity_of_string "pr -> pr";
      ity_of_string "pr -> pr"
    ];
  [
    (* check that intersection of common types from different arguments works *)
    "type_check-6" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.singleton_of_envm ty_pr @@
           mk_fake_envm (NTTyMap.of_seq @@ List.to_seq [
               ((2, ty_of_string "(pr -> pr) -> (np -> pr) -> np -> pr"), false);
               ((3, ty_of_string "(np -> np) -> np -> np"), false)
             ]) false @@
           new env [|
             ity_of_string "pr -> pr";
             ity_of_string "(np -> pr) /\\ (np -> np)";
             ity_of_string "np"
           |]) @@
        type_check_nt_wo_env typing hg 1 ty_pr false false l
      );

    (* check that branching works *)
    "type_check-7" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list [
              (ty_pr, [
                 mk_fake_envm empty_used_nts true @@ senv hg 4 0 "pr";
                 mk_fake_envm empty_used_nts true @@ senv hg 4 0 "np"
               ])
            ]) @@
        type_check_nt_wo_env typing hg 4 ty_pr false false l
      );

    (* check that branching works *)
    "type_check-8" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list [
              (ty_np, [
                 mk_fake_envm empty_used_nts false @@ senv hg 4 0 "pr";
                 mk_fake_envm empty_used_nts false @@ senv hg 4 0 "np"
               ])
            ]) @@
        type_check_nt_wo_env typing hg 4 ty_np false false l
      );

    (* Basic creation of bindings without a product *)
    "binding2envms-1" >:: (fun _ ->
        assert_equal_envms
          (Envms.of_list_empty_meta [
              new env @@ [|
                ity_of_string "pr -> pr";
                ity_of_string "pr -> pr";
                ity_of_string "pr -> pr"
              |];
              new env @@ [|
                ity_of_string "pr -> pr";
                ity_of_string "np -> np";
                ity_of_string "np -> pr"
              |]
            ]) @@
        typing#binding2envms 3 None None [(0, 0, id0_0)]
      );

    (* Basic creation of bindings with mask without all but first variables, without product *)
    "binding2envms-2" >:: (fun _ ->
        assert_equal_envms
          (Envms.of_list_empty_meta [
              new env @@ [|
                ity_of_string "pr -> pr";
                ity_of_string "T";
                ity_of_string "T"
              |]
            ]) @@
        typing#binding2envms 3 (Some (SortedVars.of_list [(0, 0)])) None
          [(0, 0, id0_0)]
      );

    (* Creation of bindings with mask and fixed hty of hterms. *)
    "binding2envms-3" >:: (fun _ ->
        assert_equal_envms
          (Envms.of_list_empty_meta [
              new env @@ [|
                ity_of_string "np -> pr";
                ity_of_string "T";
                ity_of_string "T"
              |]
            ]) @@
        typing#binding2envms 3 (Some (SortedVars.of_list [(0, 0)]))
          (Some (id0_0, [ity_of_string "np -> pr"; ity_of_string "pr"; ity_of_string "np"]))
          [(0, 0, id0_0)]
      );
  ]

(** Grammar that tests typing with duplication in N1 when N2 receives two the same arguments. It
    also tests no duplication when these arguments are different in N3. It also has a binding where
    N4 is partially applied, so it has two elements from two different nonterminals. *)
let grammar_dup () = mk_grammar
    [|
      (* N0 -> b (b (N1 a) (N3 a a)) (N5 N4 (a e)) *)
      (0, App (App (
           TE B,
           App (App (
               TE B,
               App (NT 2, TE A)),
                App (App (NT 3, TE A), App (TE A, TE E)))),
               App (App (NT 5, NT 4), App (TE A, TE E))));
      (* N1 x y z -> x (y z) *)
      (3, App (Var (1, 0), App  (Var (1, 1), Var (1, 2))));
      (* N2 x -> N1 x x (a e) *)
      (1, App (App (App (NT 1, Var (2, 0)), Var (2, 0)), App (TE A, TE E)));
      (* N3 x y -> N1 x x y *)
      (2, App (App (App (NT 1, Var (3, 0)), Var (3, 0)), Var (3, 1)));
      (* N4 x y z -> N1 x y z *)
      (3, App (App (App (NT 1, Var (4, 0)), Var (4, 1)), Var (4, 2)));
      (* N5 x -> N6 (x a) *)
      (1, App (NT 6, App (Var (5, 0), TE A)));
      (* N6 x -> x a *)
      (1, App (Var (6, 0), TE A))
    |]

let typing_dup_test () =
  let hg, typing = mk_typing @@ grammar_dup () in
  ignore @@ typing#add_nt_ty 1 @@ ty_of_string "(pr -> pr) -> (pr -> pr) -> pr -> np";
  ignore @@ typing#add_nt_ty 1 @@ ty_of_string "(pr -> np) -> (pr -> np) -> pr -> np";
  [
    (* All valid typings of x type check, because the application is already productive due to
       a e being productive. *)
    "type_check-9" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list [
              (ty_pr, [
                  mk_fake_envm (nt_ty_used_once 1 (
                      ty_of_string "(pr -> pr) -> (pr -> pr) -> pr -> np")) true @@
                  senv hg 2 0 "pr -> pr";
                  mk_fake_envm (nt_ty_used_once 1 (
                      ty_of_string "(pr -> np) -> (pr -> np) -> pr -> np")) true @@
                  senv hg 2 0 "pr -> np"
                ])
            ]) @@
        type_check_nt_wo_env typing hg 2 ty_pr false false l
      );

    (* No valid environment, because a e is productive and makes the application with it as
       argument productive. *)
    "type_check-10" >:: (fun _ ->
        assert_equal_tes
          TargetEnvms.empty @@
        type_check_nt_wo_env typing hg 2 ty_np false false l
      );

    (* Only one valid env when there is a duplication. Since everything in N1 is a variable,
       there is no way to create pr terms without a duplication. The x : pr -> pr typing
       causes a duplication and type checks. Typing x : pr -> np does not type check, because
       it is not productive, so it is not a duplication. y : pr is forced by there being no
       known typing of the head with unproductive last argument. *)
    "type_check-11" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.singleton_of_envm ty_pr @@
           mk_fake_envm (nt_ty_used_once 1 (
               ty_of_string "(pr -> pr) -> (pr -> pr) -> pr -> np")) true @@
           new env [|
             ity_of_string "pr -> pr";
             ity_of_string "pr"
           |]) @@
        type_check_nt_wo_env typing hg 3 ty_pr false false l
      );

    (* Only one valid env when there is no duplication. This is exactly the opposite of the test
       above with x : pr -> np passing and x : pr -> pr failing and y : pr being forced. *)
    "type_check-12" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.singleton_of_envm ty_np @@
           mk_fake_envm (nt_ty_used_once 1 (
               ty_of_string "(pr -> np) -> (pr -> np) -> pr -> np")) false @@
           new env [|
             ity_of_string "pr -> np";
             ity_of_string "pr"
           |]) @@
        type_check_nt_wo_env typing hg 3 ty_np false false l
      );

    (* Similar to test 11, but this time there are separate variables used for first
       and second argument, so there is no place for duplication. This means that there is no
       way to achieve productivity. *)
    "type_check-13" >:: (fun _ ->
        assert_equal_tes
          TargetEnvms.empty @@
        type_check_nt_wo_env typing hg 4 ty_pr false false l
      );

    (* TODO update tests from here *)
    (* Similar to test 12, but this time the duplication cannot happen. *)
    "type_check-14" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list @@ [
              (ty_np, [
                  mk_fake_envm (nt_ty_used_once 1 (
                      ty_of_string "(pr -> pr) -> (pr -> pr) -> pr -> np")) false @@
                  new env [|
                    ity_of_string "pr -> pr";
                    ity_of_string "pr -> pr";
                    ity_of_string "pr"
                  |];
                  mk_fake_envm (nt_ty_used_once 1 (
                      ty_of_string "(pr -> np) -> (pr -> np) -> pr -> np")) false @@
                  new env [|
                    ity_of_string "pr -> np";
                    ity_of_string "pr -> np";
                    ity_of_string "pr"
                  |]
                ])
            ]
          ) @@
        type_check_nt_wo_env typing hg 4 ty_np false false l
      );

    (* Typing without target *)
    "type_check-15" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list @@ [
              (ty_pr, [
                  mk_fake_envm (nt_ty_used_once 1 (
                      ty_of_string "(pr -> pr) -> (pr -> pr) -> pr -> np")) true @@
                  new env [|
                    ity_of_string "pr -> pr";
                    ity_of_string "pr"
                  |]
                ]);
              (ty_np, [
                  mk_fake_envm (nt_ty_used_once 1 (
                      ty_of_string "(pr -> np) -> (pr -> np) -> pr -> np")) false @@
                  new env [|
                    ity_of_string "pr -> np";
                    ity_of_string "pr"
                  |]
                ])
            ]
          ) @@
        type_check_nt_wo_env_wo_target typing hg 3 false false l
      );
  ]

(** Grammar that has nonterminal that has binding in the form N [t] [t] for the same t. Used
    to test edge cases for bindings. *)
let grammar_double () = mk_grammar
    [|
      (* N0 -> N1 a e *)
      (0, App (App (NT 1, TE A), TE E));
      (* N1 x y -> b (x y) (N1 (N2 y) y)
         0CFA will find binding and N1 [N2 y; y] and N0 [a; e]. *)
      (2, App (App (
           TE B,
           App (Var (1, 0), Var (1, 1))),
               App (App (NT 1, App (NT 2, Var (1, 1))), Var (1, 1)))
      );
      (* N2 x y -> x
         0CFA will find a binding N2 [y] [y]
         e.g., np -> T -> np *)
      (2, Var (2, 0))
    |]

let typing_double_test () =
  let hg, typing = mk_typing @@ grammar_double () in
  let id0_ae = hg#locate_hterms_id 0 [0] in
  ignore @@ typing#add_hterms_hty id0_ae @@
  [ity_of_string "np -> pr /\\ pr -> pr"; ity_of_string "np"];
  let id1_y = hg#locate_hterms_id 1 [0; 0; 0] in
  ignore @@ typing#add_hterms_hty id1_y @@ [ity_of_string "np"];
  [
    (* Creation of bindings with fixed hty of hterms when there are two copies of
       fixed hterms in a binding and without mask. *)
    "binding2envms-4" >:: (fun _ ->
        assert_equal_envms
          (Envms.of_list_empty_meta [
              new env @@ [|
                ity_of_string "pr";
                ity_of_string "np"
              |];
              new env @@ [|
                ity_of_string "np";
                ity_of_string "pr"
              |];
              new env @@ [|
                ity_of_string "pr";
                ity_of_string "pr"
              |]
            ]) @@
        typing#binding2envms 2 None
          (Some (id1_y, [ity_of_string "pr"]))
          [(0, 0, id1_y); (1, 1, id1_y)]
      );

    (* Creation of bindings with mask and with fixed hty of hterms when there are
       two copies of fixed hterms in a binding. *)
    "binding2envms-5" >:: (fun _ ->
        assert_equal_envms
          (Envms.of_list_empty_meta [
              new env @@ [|
                ity_of_string "pr";
                ity_of_string "T"
              |];
              new env @@ [|
                ity_of_string "np";
                ity_of_string "T"
              |]
            ]) @@
        typing#binding2envms 2 (Some (SortedVars.singleton (2, 0)))
          (Some (id1_y, [ity_of_string "pr"]))
          [(0, 0, id1_y); (1, 1, id1_y)]
      );
    
    (* Creation of bindings without mask or forced hty when there are two copies of same
       hterms in a binding. *)
    "binding2envms-6" >:: (fun _ ->
        assert_equal_envms
          (Envms.of_list_empty_meta [
              new env @@ [|
                ity_of_string "np";
                ity_of_string "np"
              |]
            ]) @@
        typing#binding2envms 2 None None [(0, 0, id1_y); (1, 1, id1_y)]
      );

    (* Creation of bindings without mask and without fixed hty of hterms. *)
    "binding2envms-7" >:: (fun _ ->
        assert_equal_envms
          (Envms.of_list_empty_meta [
              new env @@ [|
                ity_of_string "np -> pr /\\ pr -> pr";
                ity_of_string "np"
              |]
            ]) @@
        typing#binding2envms 2 None None [(0, 0, id0_ae)]
      );

    (* Creation of bindings with mask and fixed hty of hterms. *)
    "binding2envms-8" >:: (fun _ ->
        assert_equal_envms
          (Envms.of_list_empty_meta [
              new env @@ [|
                ity_of_string "np -> pr";
                ity_of_string "T"
              |]
            ]) @@
        typing#binding2envms 2
          (Some (SortedVars.singleton (1, 0)))
          (Some (id0_ae, [ity_of_string "np -> pr"; ity_of_string "np"]))
          [(0, 0, id0_ae)]
      );

    (* Creation of bindings with mask and fixed hty of hterms. *)
    "binding2envms-9" >:: (fun _ ->
        assert_equal_envms
          (Envms.of_list_empty_meta [
              new env @@ [|
                ity_of_string "T";
                ity_of_string "np"
              |]
            ]) @@
        typing#binding2envms 2
          (Some (SortedVars.singleton (1, 1)))
          (Some (id0_ae, [ity_of_string "np -> pr"; ity_of_string "np"]))
          [(0, 0, id0_ae)]
      );

    (* Creation of bindings with fixed hty of hterms when there are two copies of
       fixed hterms in a binding and without mask. *)
    "binding2envms-10" >:: (fun _ ->
        assert_equal_envms
          (Envms.of_list_empty_meta [
              new env @@ [|
                ity_of_string "pr";
                ity_of_string "np";
                ity_of_string "pr -> pr /\\ np -> pr";
                ity_of_string "np";
                ity_of_string "pr -> pr /\\ np -> pr";
                ity_of_string "np"
              |];
              new env @@ [|
                ity_of_string "np";
                ity_of_string "pr";
                ity_of_string "pr -> pr /\\ np -> pr";
                ity_of_string "np";
                ity_of_string "pr -> pr /\\ np -> pr";
                ity_of_string "np"
              |];
              new env @@ [|
                ity_of_string "pr";
                ity_of_string "pr";
                ity_of_string "pr -> pr /\\ np -> pr";
                ity_of_string "np";
                ity_of_string "pr -> pr /\\ np -> pr";
                ity_of_string "np"
              |]
            ]) @@
        typing#binding2envms 6 None
          (Some (id1_y, [ity_of_string "pr"]))
          [(0, 0, id1_y); (1, 1, id1_y); (2, 3, id0_ae); (4, 5, id0_ae)]
      );

    (* Creation of bindings fixed hty of hterms, but no variables. *)
    "binding2envms-11" >:: (fun _ ->
        assert_equal_envms
          (Envms.of_list_empty_meta [
              empty_env 0
            ]) @@
        typing#binding2envms 0
          None
          (Some (id0_ae, [ity_of_string "np -> pr"; ity_of_string "np"]))
          []
      );

    (* Creation of bindings with no variables. *)
    "binding2envms-12" >:: (fun _ ->
        assert_equal_envms
          (Envms.of_list_empty_meta [
              empty_env 0
            ]) @@
        typing#binding2envms 0 None None []
      );
  ]



(** Grammar to test uncategorized typing schemes. *)
let grammar_misc () = mk_grammar
    [|
      (* N0 -> N1 e *)
      (0, App (NT 1, TE E));
      (* N1 x -> a x *)
      (1, App (TE A, Var (1, 0)))
    |]

let typing_misc_test () =
  let hg, typing = mk_typing @@ grammar_misc () in
  [
    (* Typing a x without target should not yield np target. *)
    "type_check-16" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list @@ [
              (ty_pr, [
                  mk_fake_envm empty_used_nts true @@
                  new env [|
                    ity_of_string "pr"
                  |]
                ])
            ]
          ) @@
        typing#type_check (hg#nt_body 1) None (Left (senv hg 1 0 "pr")) false false l
      );

    (* Typing a x without target should not yield np target. *)
    "type_check-17" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list @@ [
              (ty_pr, [
                  mk_fake_envm empty_used_nts true @@
                  new env [|
                    ity_of_string "np"
                  |]
                ])
            ]
          ) @@
        typing#type_check (hg#nt_body 1) None (Left (senv hg 1 0 "np")) false false l
      );

    (* Typing a x without target should not yield np target. *)
    "type_check-18" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list @@ [
              (ty_pr, [
                  mk_fake_envm empty_used_nts true @@
                  new env [|
                    ity_of_string "pr"
                  |]
                ]);
              (ty_pr, [
                  mk_fake_envm empty_used_nts true @@
                  new env [|
                    ity_of_string "np"
                  |]
                ])
            ]
          ) @@
        typing#type_check (hg#nt_body 1) None (Right (hg#nt_arity 1)) false false l
      );
  ]



let typing_test () : test =
  init_flags ();
  "typing" >:::
  typing_e_test () @
  typing_ax_test () @
  typing_xyyz_test () @
  typing_dup_test () @
  typing_double_test () @
  typing_misc_test ()



let cfa_test () : test =
  init_flags ();
  let hg_xyyz = mk_hgrammar @@ grammar_xyyz () in
  let cfa_xyyz = mk_cfa hg_xyyz in
  let hg_dup = mk_hgrammar @@ grammar_dup () in
  let cfa_dup = mk_cfa hg_dup in
  let hg_double = mk_hgrammar @@ grammar_double () in
  let cfa_double = mk_cfa hg_double in
  "cfa" >:::
  [
    (* empty binding with no variables *)
    "nt_binding-1" >:: (fun _ ->
        assert_equal
          [[]]
          (cfa_xyyz#lookup_nt_bindings 0)
      );

    (* single binding, directly *)
    "nt_binding-2" >:: (fun _ ->
        assert_equal
          [
            [(0, 2, List.hd @@ snd @@ hg_xyyz#nt_body 0)]
          ]
          (cfa_xyyz#lookup_nt_bindings 1)
      );

    (* two bindings, both indirectly due to partial application *)
    "nt_binding-3" >:: (fun _ ->
        assert_equal
          [
            "[nt2v2]";
            "[nt3v1]"
          ]
          (List.sort Pervasives.compare @@ List.map (fun binding ->
               match binding with
               | [(_, _, id)] -> hg_xyyz#string_of_hterms id
               | _ -> failwith "fail"
             ) @@ cfa_xyyz#lookup_nt_bindings 4)
      );

    (* no bindings when unreachable *)
    "nt_binding-4" >:: (fun _ ->
        assert_equal
          []
          (cfa_xyyz#lookup_nt_bindings 5)
      );

    (* binding with args from different nonterminals *)
    "nt_binding-5" >:: (fun _ ->
        assert_equal
          [
            [
              (* a in N5 *)
              (0, 0, hg_dup#locate_hterms_id 5 [0; 0; 0]);
              (* a <var> in N6 *)
              (1, 2, hg_dup#locate_hterms_id 6 [0])
            ]
          ]
          (cfa_dup#lookup_nt_bindings 4)
      );

    (* Two bindings for N1 in grammar_double. *)
    "nt_binding-6" >:: (fun _ ->
        assert_equal ~cmp:list_sort_eq
          [
            [
              (0, 1, hg_double#locate_hterms_id 0 [0])
            ];
            [
              (0, 1, hg_double#locate_hterms_id 1 [0; 1; 0])
            ]
          ]
          (cfa_double#lookup_nt_bindings 1)
      );
    
    (* One binding for N2 in grammar_double, a binding with two identical hterms. *)
    "nt_binding-7" >:: (fun _ ->
        assert_equal ~cmp:list_sort_eq
          [
            [
              (* N2 [y] [y] after substitution in N1 *)
              (0, 0, hg_double#locate_hterms_id 1 [0; 0; 0]);
              (1, 1, hg_double#locate_hterms_id 1 [0; 0; 0])
            ]
          ]
          (cfa_double#lookup_nt_bindings 2)
      );
    
    (* checking that cfa detected that in N0 nonterminal N1 was applied to N4 *)
    "var_binding-1" >:: (fun _ ->
        assert_equal
          [
            (HNT 4, [])
          ]
          (cfa_xyyz#lookup_binding_var (1, 1))
      );
  ]



let proof_test () : test =
  init_flags ();
  "proof" >::: [
    "proof-1" >:: (fun _ ->
        match Main.parse_and_report_finiteness @@ Some "examples/multiple_usages_inf.inf" with
        | Infinite cycle_proof_str ->
          assert_regexp_count 1 (Str.regexp_string "I (x2)") cycle_proof_str;
          assert_regexp_count 3 (Str.regexp_string "(+)") cycle_proof_str;
          assert_regexp_count 1 (Str.regexp_string "(x2)") cycle_proof_str;
          assert_regexp_count 2 (Str.regexp_string "x#1") cycle_proof_str;
          assert_regexp_count 2 (Str.regexp_string "x#2") cycle_proof_str;
          assert_regexp_count 0 (Str.regexp_string "C#1") cycle_proof_str;
          assert_regexp_count 0 (Str.regexp_string "S#1") cycle_proof_str;
          assert_regexp_count 0 (Str.regexp_string "I#1") cycle_proof_str;
          assert_regexp_count 1 (Str.regexp "C :.*\n.*C :") cycle_proof_str;
          assert_regexp_count 1 (Str.regexp "A :.*/\\\\") cycle_proof_str
        | Finite | Unknown ->
          failwith "Expected infinite saturation result"
      );
  ]



let examples_test () : test =
  init_flags ();
  let filenames_in_dir = List.filter (fun f -> String.length f > 8)
      (Array.to_list (Sys.readdir "examples")) in
  let inf_filenames = List.filter (fun f ->
      String.sub f (String.length f - 8) 8 = "_inf.inf") filenames_in_dir in
  let fin_filenames = List.filter (fun f ->
      String.sub f (String.length f - 8) 8 = "_fin.inf") filenames_in_dir in
  let path filename = Some (String.concat "" ["examples/"; filename]) in
  let run filename =
    if String.length filename > 15 &&
       String.sub filename (String.length filename - 15) 7 = "_unsafe" then
      begin
        let unsafe_before = !Flags.force_unsafe in
        Flags.force_unsafe := true;
        let res = Main.parse_and_report_finiteness (path filename) in
        Flags.force_unsafe := unsafe_before;
        res
      end
    else
      Main.parse_and_report_finiteness (path filename)
  in
  "Examples" >::: [
    "Infinite examples" >::: List.map (fun filename ->
        filename >:: (fun _ ->
            assert_equal ~printer:id "infinite" @@
            Saturation.string_of_infsat_result @@ run filename))
      inf_filenames;
    "Finite examples" >::: List.map (fun filename ->
        filename >:: (fun _ ->
            assert_equal ~printer:Saturation.string_of_infsat_result Finite @@
            run filename))
      fin_filenames
  ]



let tests () = [
  utilities_test ();
  dfg_test ();
  conversion_test ();
  cfa_test ();
  te_test ();
  type_test ();
  typing_test ();
  proof_test ();
  examples_test ()
]
