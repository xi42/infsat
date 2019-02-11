open Grammar
open GrammarCommon
open Main
open OUnit2
open Type
open Typing

let init_flags () =
  Flags.debugging := true;
  Flags.verbose := true

let mk_grammar nonterminals var_names rules =
  let g = new grammar nonterminals var_names rules in
  Stype.eta_expand g;
  g

let grammarE = mk_grammar
    [|
      ("S", O)
    |]
    [||]
    [|
      (0, T E)
    |]

let mk_hgrammar g =
  new HGrammar.hgrammar g

let mk_cfa g hg =
  let hg =
    match hg with
    | None -> mk_hgrammar g
    | Some g -> g
  in
  let cfa = new Cfa.cfa g hg in
  cfa#expand;
  cfa#mk_binding_depgraph;
  cfa

let mk_typing g =
  let hg = mk_hgrammar g in
  let cfa = mk_cfa g (Some hg) in
  (hg, new Typing.typing hg cfa)

let typing_test : test =
  let hgE, typingE = mk_typing grammarE in
  init_flags ();
  "typing" >::: [
    "annotate_args" >:: (fun _ ->
        assert_equal (
          typingE#annotate_args
            [1; 2]
            (TyList.singleton
               (Fun (2, TyList.singleton NP, Fun(3, TyList.singleton PR, Fun(4, TyList.empty, PR))))
            )
        ) [
          ([(1, TyList.singleton NP); (2, TyList.singleton PR)], true)
        ]
      );

    "infer_wo_venv 1" >:: (fun _ ->
        assert_equal (
          typingE#infer_wo_venv (hgE#find_term (T E)) NP false false
        ) [VEnv.empty]
      );

    "infer_wo_venv 2" >:: (fun _ ->
        assert_equal (
          typingE#infer_wo_venv (hgE#find_term (T E)) NP false true
        ) []
      );

    "infer_wo_venv 3" >:: (fun _ ->
        assert_equal (
          typingE#infer_wo_venv (hgE#find_term (T E)) NP true false
        ) [VEnv.empty]
      );
  ]

let examples_test : test =
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
            assert_equal (Main.parse_and_report_finiteness (path filename)) false))
      inf_filenames;
    "Finite examples" >::: List.map (fun filename ->
        filename >:: (fun _ ->
            assert_equal (Main.parse_and_report_finiteness (path filename)) true))
      fin_filenames]

let _ =
  run_test_tt_main (test_list [
      typing_test;
      (* examples_test *)
    ])
