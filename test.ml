
open Binding
open DuplicationFactorGraph
open Environment
open Grammar
open GrammarCommon
open HGrammar
open HtyStore
open Main
open OUnit2
open TargetEnvms
open Type
open Typing
open Utilities

(* --- helper functions --- *)

let init_flags () =
  Flags.verbose_all := true;
  Flags.propagate_flags ()

let assert_equal_envms envms1 envms2 =
  assert_equal ~printer:Envms.to_string ~cmp:Envms.equal
    (Envms.with_empty_temp_flags envms1) (Envms.with_empty_temp_flags envms2)

let assert_equal_tes te1 te2 =
  assert_equal ~printer:TargetEnvms.to_string ~cmp:TargetEnvms.equal
    (TargetEnvms.with_empty_temp_flags te1) (TargetEnvms.with_empty_temp_flags te2)

let mk_grammar rules =
  let nonterminals = Array.mapi (fun i _ -> ("N" ^ string_of_int i, O)) rules in
  let g = new grammar nonterminals [||] rules in
  print_string @@ "Creating grammar:\n" ^
                  g#grammar_info;
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

let dfg_test () : test =
  "dfg" >::: [
    (* one node, no edges *)
    "dfg-0" >:: (fun _ ->
        assert_equal false @@
        (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex 0 ty_np empty_used_nts false;
          dfg
        )#find_positive_cycle 0 ty_np
      );

    (* unreachable loop *)
    "dfg-1" >:: (fun _ ->
        assert_equal false @@
        (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex 0 ty_np empty_used_nts false;
          ignore @@ dfg#add_vertex 0 ty_pr (nt_ty_used_once 0 ty_pr) true;
          dfg
        )#find_positive_cycle 0 ty_np
      );

    (* positive loop at start *)
    "dfg-2" >:: (fun _ ->
        assert_equal true @@
        (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex 0 ty_pr (nt_ty_used_once 0 ty_pr) true;
          dfg
        )#find_positive_cycle 0 ty_pr
      );

    (* non-positive loop at start *)
    "dfg-3" >:: (fun _ ->
        assert_equal false @@
        (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex 0 ty_np (nt_ty_used_once 0 ty_np) false;
          dfg
        )#find_positive_cycle 0 ty_np
      );

    (* non-positive and positive interconnected loops *)
    "dfg-4" >:: (fun _ ->
        assert_equal true @@
        (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex 0 ty_np (nt_ty_used_once 1 ty_np) false;
          ignore @@ dfg#add_vertex 1 ty_np (nt_ty_used_once 2 ty_pr) true;
          ignore @@ dfg#add_vertex 2 ty_pr (nt_ty_used_once 3 ty_np) false;
          ignore @@ dfg#add_vertex 3 ty_np (nt_ty_used_once 1 ty_np) false;
          ignore @@ dfg#add_vertex 1 ty_np (nt_ty_used_once 4 ty_np) false;
          ignore @@ dfg#add_vertex 4 ty_np (nt_ty_used_once 3 ty_np) false;
          dfg
        )#find_positive_cycle 0 ty_np
      );

    (* non-positive and positive interconnected loops - another order *)
    "dfg-5" >:: (fun _ ->
        assert_equal true @@
        (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex 0 ty_np (nt_ty_used_once 1 ty_np) false;
          ignore @@ dfg#add_vertex 1 ty_np (nt_ty_used_once 2 ty_pr) false;
          ignore @@ dfg#add_vertex 2 ty_pr (nt_ty_used_once 3 ty_np) false;
          ignore @@ dfg#add_vertex 3 ty_np (nt_ty_used_once 1 ty_np) false;
          ignore @@ dfg#add_vertex 1 ty_np (nt_ty_used_once 4 ty_np) true;
          ignore @@ dfg#add_vertex 4 ty_np (nt_ty_used_once 3 ty_np) false;
          dfg
        )#find_positive_cycle 0 ty_np
      );

    (* non-positive loop and positive path *)
    "dfg-6" >:: (fun _ ->
        assert_equal false @@
        (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex 0 ty_np (nt_ty_used_once 1 ty_np) false;
          ignore @@ dfg#add_vertex 1 ty_np (nt_ty_used_once 2 ty_pr) true;
          ignore @@ dfg#add_vertex 2 ty_pr (nt_ty_used_once 3 ty_np) false;
          ignore @@ dfg#add_vertex 1 ty_np (nt_ty_used_once 4 ty_np) false;
          ignore @@ dfg#add_vertex 4 ty_np (nt_ty_used_once 5 ty_np) false;
          ignore @@ dfg#add_vertex 5 ty_np (nt_ty_used_once 1 ty_np) false;
          dfg
        )#find_positive_cycle 0 ty_np
      );

    (* registering twice the same vertex *)
    "dfg-7" >:: (fun _ ->
        assert_equal true @@
        (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex 0 ty_pr (nt_ty_used_once 0 ty_pr) true;
          ignore @@ dfg#add_vertex 0 ty_pr (nt_ty_used_once 0 ty_pr) false;
          dfg
        )#find_positive_cycle 0 ty_pr
      );

    (* checking for not registered vertex *)
    "dfg-7" >:: (fun _ ->
        assert_equal false @@
        (
          let dfg = new dfg in
          ignore @@ dfg#add_vertex 0 ty_pr (nt_ty_used_once 0 ty_pr) true;
          dfg
        )#find_positive_cycle 0 ty_np
      );
  ]

let conversion_test () : test =
  (* These preterminals are defined in a way so that they should be converted to respective
     terminals from paper without creating additional terms (such as functions). *)
  let preserved_preterminals = [
    Syntax.Terminal ("a", 1, true);
    Syntax.Terminal ("b", 2, false);
    Syntax.Terminal ("e", 0, false);
    Syntax.Terminal ("id", 1, false)
  ] in
  (* This grammar aims to test all combinations of applications of terminals a, b, e with
     all possible numbers of applied arguments. It also tests that not counted terminal
     with one child is removed when it has an argument (as it is identity). And it also
     tests built-in br terminal. *)
  let test_prerules = [
    ("E", [], Syntax.PApp (Syntax.Name "e", []));
    ("A", ["x"], Syntax.PApp (Syntax.Name "a", [
         Syntax.PApp (Syntax.Name "x", [])
       ]));
    ("B", [], Syntax.PApp (Syntax.Name "b", []));
    ("Be", [], Syntax.PApp (Syntax.Name "b", [
         Syntax.PApp (Syntax.Name "e", [])
       ]));
    ("BAee", [], Syntax.PApp (Syntax.Name "b", [
         Syntax.PApp (Syntax.Name "a", [Syntax.PApp (Syntax.Name "e", [])]);
         Syntax.PApp (Syntax.Name "e", [])
       ]));
    ("X", ["x"], Syntax.PApp (Syntax.Name "x", [
         Syntax.PApp (Syntax.Name "e", [])
       ]));
    ("Xa", [], Syntax.PApp (Syntax.NT "X", [
         Syntax.PApp (Syntax.Name "a", [])
       ]));
    ("IDe", [], Syntax.PApp (Syntax.Name "id", [
         Syntax.PApp (Syntax.Name "e", [])
       ]));
    ("ID", [], Syntax.PApp (Syntax.Name "id", []));
    ("BR", [], Syntax.PApp (Syntax.Name "br", []));
    ("BRe", [], Syntax.PApp (Syntax.Name "br", [
         Syntax.PApp (Syntax.Name "e", [])
       ]));
    ("BRxy", ["x"; "y"], Syntax.PApp (Syntax.Name "br", [
         Syntax.PApp (Syntax.Name "x", []);
         Syntax.PApp (Syntax.Name "y", [])
       ]))
  ] in
  let gram = Conversion.prerules2gram (test_prerules, preserved_preterminals) in
  if !Flags.verbose_preprocessing then
    print_string @@ "Conversion test grammar:\n" ^ gram#grammar_info ^ "\n";
  "conversion" >::: [
    (* Terminals
       a -> 1 $.
       b -> 2.
       e -> 0.
       should be preserved as in the paper, without needless conversion. Therefore, there
       should be no functions apart from the one from identity without arguments, i.e.,
       exactly one extra rule. *)
    "prerules2gram-1" >:: (fun _ ->
        assert_equal ~printer:string_of_int 13 @@
        Array.length gram#rules
      );

    (* Checking that number of leaf terms is correct - nothing extra was added or removed
       aside from extra rule from identity without arguments. *)
    "prerules2gram-2" >:: (fun _ ->
        assert_equal ~printer:string_of_int 23
        gram#size
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
          (TargetEnvms.singleton ty_np @@ empty_env 0) @@
        TargetEnvms.intersect
          (TargetEnvms.singleton ty_np @@ empty_env 0)
          (TargetEnvms.singleton ty_np @@ empty_env 0)
      );

    "intersect-2" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list [
              (ty_np, [with_positive true @@ with_dup true @@
                    mk_envm_empty_flags @@ singleton_env 1 (0, 0) @@ sty ty_pr])
            ]) @@
        TargetEnvms.intersect
          (TargetEnvms.of_list_empty_flags [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_pr])
            ])
          (TargetEnvms.of_list_empty_flags [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_pr])
            ])
      );

    "intersect-3" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list_empty_flags [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np])
            ]) @@
        TargetEnvms.intersect
          (TargetEnvms.of_list_empty_flags [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np])
            ])
          (TargetEnvms.of_list_empty_flags [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np])
            ])
      );

    "intersect-4" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_envm
                      (NTTyMap.of_list [((0, ty_pr), false); ((0, ty_np), false)]) true])
            ]) @@
        TargetEnvms.intersect
          (TargetEnvms.of_list [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_envm (nt_ty_used_once 0 ty_pr) true])
            ])
          (TargetEnvms.of_list [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_envm (nt_ty_used_once 0 ty_np) true;
                    singleton_env 1 (0, 0) @@ sty ty_np |> mk_envm (nt_ty_used_once 0 ty_np) false]);
              (ty_pr, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_envm empty_used_nts false])
            ])
      );

    "intersect-5" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_envm
                      (NTTyMap.of_list [((0, ty_np), true)]) false;
                    singleton_env 1 (0, 0) @@ sty ty_np |> mk_envm
                      (NTTyMap.of_list [((0, ty_np), true)]) true]);
            ]) @@
        TargetEnvms.intersect
          (TargetEnvms.of_list [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_envm (nt_ty_used_once 0 ty_np) false])
            ])
          (TargetEnvms.of_list [
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_envm (nt_ty_used_once 0 ty_np) true]);
              (ty_np, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_envm (nt_ty_used_once 0 ty_np) false]);
              (ty_pr, [singleton_env 1 (0, 0) @@ sty ty_np |> mk_envm empty_used_nts false])
            ])
      );

    "intersect-6" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list_empty_flags [
              (ty_np, [singleton_env 2 (0, 0) @@ ity_of_string "pr /\\ np";
                    singleton_env 2 (0, 1) @@ ity_of_string "pr /\\ np";
                    new env [|sty ty_np; sty ty_pr|];
                    new env [|sty ty_pr; sty ty_np|]
                   ]);
            ]) @@
        TargetEnvms.intersect
          (TargetEnvms.of_list_empty_flags [
              (ty_np, [singleton_env 2 (0, 0) @@ sty ty_np]);
              (ty_np, [singleton_env 2 (0, 1) @@ sty ty_np])
            ])
          (TargetEnvms.of_list_empty_flags [
              (ty_np, [singleton_env 2 (0, 0) @@ sty ty_pr]);
              (ty_np, [singleton_env 2 (0, 1) @@ sty ty_pr])
            ])
      );

    (*
    "intersect-7" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list_empty_flags [
              (ty_np, [singleton_env 2 (0, 0) @@ ity_of_string "pr /\\ np";
                    singleton_env 2 (0, 1) @@ ity_of_string "pr /\\ np";
                    new env [|sty ty_np; sty ty_pr|];
                    new env [|sty ty_pr; sty ty_np|]
                   ]);
            ]) @@
        TargetEnvms.intersect
          (TargetEnvms.of_list_empty_flags [
              (ty_np, [singleton_env 2 (0, 0) @@ sty ty_np]);
              (ty_np, [singleton_env 2 (0, 1) @@ sty ty_np])
            ])
          (TargetEnvms.of_list_empty_flags [
              (ty_np, [singleton_env 2 (0, 2) @@ sty ty_np])
            ])
      );
*)
    "size-1" >:: (fun _ ->
        assert_equal ~printer:string_of_int 1 @@
        TargetEnvms.size @@
        TargetEnvms.singleton ty_np @@
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
          (TargetEnvms.singleton ty_np @@ empty_env @@ hg#nt_arity 0)
          (type_check_nt_wo_env typing hg 0 ty_np false false)
      );

    (* checking basic functionality of forcing pr vars *)
    "type_check-2" >:: (fun _ ->
        assert_equal_tes
          TargetEnvms.empty
          (type_check_nt_wo_env typing hg 0 ty_np false true)
      );

    (* checking that forcing no pr vars does not break anything when there are only terminals *)
    "type_check-3" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.singleton ty_np @@ empty_env @@ hg#nt_arity 0)
          (type_check_nt_wo_env typing hg 0 ty_np true false)
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
                 mk_envm empty_used_nts true @@ senv hg 1 0 "pr";
                 mk_envm empty_used_nts true @@ senv hg 1 0 "np"
              ])
           ])
          (type_check_nt_wo_env typing hg 1 ty_pr false false)
      );

    (* check that a x : np does not type check *)
    "type_check-5" >:: (fun _ ->
        assert_equal_tes
          TargetEnvms.empty
          (type_check_nt_wo_env typing hg 1 ty_np false false)
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
           mk_envm (NTTyMap.of_seq @@ List.to_seq [
               ((2, ty_of_string "(pr -> pr) -> (np -> pr) -> np -> pr"), false);
               ((3, ty_of_string "(np -> np) -> np -> np"), false)
             ]) false @@
           new env [|
             ity_of_string "pr -> pr";
             ity_of_string "(np -> pr) /\\ (np -> np)";
             ity_of_string "np"
           |]) @@
        type_check_nt_wo_env typing hg 1 ty_pr false false
      );

    (* check that branching works *)
    "type_check-7" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list [
              (ty_pr, [
                 mk_envm empty_used_nts true @@ senv hg 4 0 "pr";
                 mk_envm empty_used_nts true @@ senv hg 4 0 "np"
               ])
            ]) @@
        type_check_nt_wo_env typing hg 4 ty_pr false false
      );

    (* check that branching works *)
    "type_check-8" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list [
              (ty_np, [
                 mk_envm empty_used_nts false @@ senv hg 4 0 "pr";
                 mk_envm empty_used_nts false @@ senv hg 4 0 "np"
               ])
            ]) @@
        type_check_nt_wo_env typing hg 4 ty_np false false
      );

    (* Basic creation of bindings without a product *)
    "binding2envms-1" >:: (fun _ ->
        assert_equal_envms
          (Envms.of_list_empty_flags [
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
          (Envms.of_list_empty_flags [
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
          (Envms.of_list_empty_flags [
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
                  mk_envm (nt_ty_used_once 1 @@
                           ty_of_string "(pr -> pr) -> (pr -> pr) -> pr -> np") true @@
                  senv hg 2 0 "pr -> pr";
                  mk_envm (nt_ty_used_once 1 @@
                           ty_of_string "(pr -> np) -> (pr -> np) -> pr -> np") true @@
                  senv hg 2 0 "pr -> np"
                ])
            ])
          (type_check_nt_wo_env typing hg 2 ty_pr false false)
      );

    (* No valid environment, because a e is productive and makes the application with it as
       argument productive. *)
    "type_check-10" >:: (fun _ ->
        assert_equal_tes
          TargetEnvms.empty
          (type_check_nt_wo_env typing hg 2 ty_np false false)
      );

    (* Only one valid env when there is a duplication. Since everything in N1 is a variable,
       there is no way to create pr terms without a duplication. The x : pr -> pr typing
       causes a duplication and type checks. Typing x : pr -> np does not type check, because
       it is not productive, so it is not a duplication. y : pr is forced by there being no
       known typing of the head with unproductive last argument. *)
    "type_check-11" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.singleton_of_envm ty_pr @@
           mk_envm (nt_ty_used_once 1 @@
                    ty_of_string "(pr -> pr) -> (pr -> pr) -> pr -> np") true @@
           new env [|
             ity_of_string "pr -> pr";
             ity_of_string "pr"
           |])
          (type_check_nt_wo_env typing hg 3 ty_pr false false)
      );

    (* Only one valid env when there is no duplication. This is exactly the opposite of the test
       above with x : pr -> np passing and x : pr -> pr failing and y : pr being forced. *)
    "type_check-12" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.singleton_of_envm ty_np @@
           mk_envm (nt_ty_used_once 1 @@
                    ty_of_string "(pr -> np) -> (pr -> np) -> pr -> np") false @@
           new env [|
             ity_of_string "pr -> np";
             ity_of_string "pr"
           |])
          (type_check_nt_wo_env typing hg 3 ty_np false false)
      );

    (* Similar to test 11, but this time there are separate variables used for first
       and second argument, so there is no place for duplication. This means that there is no
       way to achieve productivity. *)
    "type_check-13" >:: (fun _ ->
        assert_equal_tes
          TargetEnvms.empty
          (type_check_nt_wo_env typing hg 4 ty_pr false false)
      );

    (* TODO update tests from here *)
    (* Similar to test 12, but this time the duplication cannot happen. *)
    "type_check-14" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list @@ [
              (ty_np, [
                  mk_envm (nt_ty_used_once 1 @@
                           ty_of_string "(pr -> pr) -> (pr -> pr) -> pr -> np") false @@
                  new env [|
                    ity_of_string "pr -> pr";
                    ity_of_string "pr -> pr";
                    ity_of_string "pr"
                  |];
                  mk_envm (nt_ty_used_once 1 @@
                           ty_of_string "(pr -> np) -> (pr -> np) -> pr -> np") false @@
                  new env [|
                    ity_of_string "pr -> np";
                    ity_of_string "pr -> np";
                    ity_of_string "pr"
                  |]
                ])
            ]
          )
          (type_check_nt_wo_env typing hg 4 ty_np false false)
      );

    (* Typing without target *)
    "type_check-15" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list @@ [
              (ty_pr, [
                  mk_envm (nt_ty_used_once 1 @@
                           ty_of_string "(pr -> pr) -> (pr -> pr) -> pr -> np") true @@
                  new env [|
                    ity_of_string "pr -> pr";
                    ity_of_string "pr"
                  |]
                ]);
              (ty_np, [
                  mk_envm (nt_ty_used_once 1 @@
                           ty_of_string "(pr -> np) -> (pr -> np) -> pr -> np") false @@
                  new env [|
                    ity_of_string "pr -> np";
                    ity_of_string "pr"
                  |]
                ])
            ]
          )
          (type_check_nt_wo_env_wo_target typing hg 3 false false)
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
          (Envms.of_list_empty_flags [
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
          (Envms.of_list_empty_flags [
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
          (Envms.of_list_empty_flags [
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
          (Envms.of_list_empty_flags [
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
          (Envms.of_list_empty_flags [
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
          (Envms.of_list_empty_flags [
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
          (Envms.of_list_empty_flags [
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
          (Envms.of_list_empty_flags [
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
          (Envms.of_list_empty_flags [
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
                  mk_envm empty_used_nts true @@
                  new env [|
                    ity_of_string "pr"
                  |]
                ])
            ]
          )
          (typing#type_check (hg#nt_body 1) None (Left (senv hg 1 0 "pr")) false false)
      );

    (* Typing a x without target should not yield np target. *)
    "type_check-17" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list @@ [
              (ty_pr, [
                  mk_envm empty_used_nts true @@
                  new env [|
                    ity_of_string "np"
                  |]
                ])
            ]
          )
          (typing#type_check (hg#nt_body 1) None (Left (senv hg 1 0 "np")) false false)
      );

    (* Typing a x without target should not yield np target. *)
    "type_check-18" >:: (fun _ ->
        assert_equal_tes
          (TargetEnvms.of_list @@ [
              (ty_pr, [
                  mk_envm empty_used_nts true @@
                  new env [|
                    ity_of_string "pr"
                  |]
                ]);
              (ty_pr, [
                  mk_envm empty_used_nts true @@
                  new env [|
                    ity_of_string "np"
                  |]
                ])
            ]
          )
          (typing#type_check (hg#nt_body 1) None (Right (hg#nt_arity 1)) false false)
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

let examples_test () : test =
  init_flags ();
  let filenames_in_dir = List.filter (fun f -> String.length f > 8)
      (Array.to_list (Sys.readdir "examples")) in
  let inf_filenames = List.filter (fun f ->
      String.sub f (String.length f - 8) 8 = "_inf.inf") filenames_in_dir in
  let fin_filenames = List.filter (fun f ->
      String.sub f (String.length f - 8) 8 = "_fin.inf") filenames_in_dir in
  let path filename = Some (String.concat "" ["examples/"; filename]) in
  "Examples" >::: [
    "Infinite examples" >::: List.map (fun filename ->
        filename >:: (fun _ ->
            assert_equal ~printer:string_of_bool false
              (Main.parse_and_report_finiteness (path filename))))
      inf_filenames;
    "Finite examples" >::: List.map (fun filename ->
        filename >:: (fun _ ->
            assert_equal ~printer:string_of_bool true
              (Main.parse_and_report_finiteness (path filename))))
      fin_filenames]

let tests () = [
  utilities_test ();
  dfg_test ();
  conversion_test ();
  cfa_test ();
  te_test ();
  type_test ();
  typing_test ();
  examples_test ()
]
