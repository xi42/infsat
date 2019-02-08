open Main
open OUnit2
open Type

let init_flags () =
  Flags.debugging := true;
  Flags.verbose := true

let typing_test : test =
  init_flags ();
  Flags.debugging := true;
  let input = Main.parse_file "examples/complex_inf.inf" in
  let grammar = Conversion.prerules2gram input in
  Stype.eta_expand grammar;
  let hgrammar = new HGrammar.hgrammar grammar in
  let cfa = new Cfa.cfa grammar hgrammar in
  cfa#expand;
  cfa#mk_binding_depgraph;
  let typing = new Typing.typing hgrammar cfa in
  let nhv_id = grammar#nt_with_name "NoHeadVars" in
  "annotate_args" >::: [
    "case1" >:: (fun _ ->
        assert_equal (
          typing#annotate_args
            [1; 2]
            (TyList.singleton
               (Fun (2, TyList.singleton NP, Fun(3, TyList.singleton PR, Fun(4, TyList.empty, PR))))
            )
        ) [
          ([|(1, TyList.singleton NP); (2, TyList.singleton PR)|], true)
        ]
      )
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
