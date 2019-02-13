open Grammar
open GrammarCommon
open Main
open OUnit2
open Type
open Typing
open Utilities

(* --- helper functions --- *)

let init_flags () =
  Flags.debugging := true;
  Flags.verbose := !Flags.debugging

let assert_equal_venvls venvl1 venvl2 =
  assert_equal ~printer:string_of_venvl (sort_venvl venvl1) (sort_venvl venvl2)

let mk_grammar rules =
  let nonterminals = Array.mapi (fun i _ -> ("N" ^ string_of_int i, O)) rules in
  let g = new grammar nonterminals [||] rules in
  Stype.eta_expand g;
  g

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

(* --- grammars --- *)

(** The smallest possible grammar. *)
let grammar_e = mk_grammar
    [|
      (0, T E); (* N0 -> e *)
    |]

(** Grammar that tests usage of a variable. *)
let grammar_ax = mk_grammar
    [|
      (0, App (NT 1, T E)); (* N0 -> N1 e *)
      (1, App (T A, Var (1, 0))) (* N1 x -> a x *)
    |]

(** Grammar that tests intersection - x and y are inferred from one argument in N1 rule, and y and
    z from the other. N4 tests top. *)
let grammar_xyyz = mk_grammar
    [|
      (* N0 -> N1 a N4 e *)
      (0, App (App (App (NT 1, T A), NT 4), T E));
      (* N1 x y z -> N2 x y (N3 y z) *)
      (3, App (App (App (NT 2, Var (1, 0)), Var (1, 1)), App (App (NT 3, Var (1, 1)), Var (1, 2))));
      (* N2 x y v -> x (y v) *)
      (3, App (Var (2, 0), App (Var (2, 1), Var (2, 2))));
      (* N3 y z -> y z *)
      (2, App (Var (3, 0), Var (3, 1)));
      (* N4 x -> b (a x) x *)
      (1, App (App (T B, App (T A, Var (4, 0))), Var (4, 0)))
    |]

let grammar_dup = mk_grammar
    [|
      (0, NT 0)
    |]

(* --- tests --- *)

let type_test : test =
  "type" >::: [
    "string_of_ty-1" >:: (fun _ ->
        assert_equal "pr" @@ string_of_ty PR
      );

    "string_of_ty-2" >:: (fun _ ->
        assert_equal "np -> pr" @@
        string_of_ty (mk_fun (sty NP) PR)
      );

    "string_of_ty-3" >:: (fun _ ->
        assert_equal "(np -> pr) -> np" @@
        string_of_ty (mk_fun (sty (mk_fun (sty NP) PR)) NP)
      );

    "string_of_ty-4" >:: (fun _ ->
        assert_equal "pr /\\ np -> pr" @@
        string_of_ty (mk_fun (TyList.of_list [PR; NP]) PR)
      );

    "string_of_ty-5" >:: (fun _ ->
        assert_equal "T -> pr" @@ string_of_ty (mk_fun (TyList.empty) PR)
      );

    "string_of_ty-6" >:: (fun _ ->
        assert_equal "(pr -> pr) -> (np -> pr) -> np -> pr" @@
        string_of_ty
          (mk_fun
             (sty (mk_fun (sty PR) PR))
             (mk_fun
                (sty (mk_fun (sty NP) PR))
                (mk_fun (sty NP) PR)))
      );

    "string_of_ity-1" >:: (fun _ ->
        assert_equal "(pr -> pr) /\\ (np -> np)" @@
        string_of_ity (TyList.of_list [mk_fun (sty PR) PR; mk_fun (sty NP) NP])
      );
    
    "ty_of_string-1" >:: (fun _ ->
        assert_equal ~cmp:Ty.equal PR @@ ty_of_string "pr"
      );

    "ty_of_string-2" >:: (fun _ ->
        assert_equal ~cmp:Ty.equal (mk_fun (sty NP) PR) @@ ty_of_string "np -> pr"
      );

    "ty_of_string-3" >:: (fun _ ->
        assert_equal ~cmp:Ty.equal (mk_fun (sty (mk_fun (sty NP) PR)) NP) @@
        ty_of_string "(np -> pr) -> np"
      );

    "ty_of_string-4" >:: (fun _ ->
        assert_equal ~cmp:Ty.equal (mk_fun (TyList.of_list [PR; NP]) PR) @@
        ty_of_string "pr /\\ np -> pr"
      );

    "ty_of_string-5" >:: (fun _ ->
        assert_equal ~cmp:Ty.equal (mk_fun (TyList.empty) PR) @@
        ty_of_string "T -> pr"
      );

    "ty_of_string-6" >:: (fun _ ->
        assert_equal ~cmp:Ty.equal
          (mk_fun
             (sty (mk_fun (sty PR) PR))
             (mk_fun
                (sty (mk_fun (sty NP) PR))
                (mk_fun (sty NP) PR))) @@
        ty_of_string "(pr -> pr) -> (np -> pr) -> np -> pr"
      );

    "ity_of_string-1" >:: (fun _ ->
        assert_equal ~cmp:TyList.equal
          (TyList.of_list [mk_fun (sty PR) PR; mk_fun (sty NP) NP]) @@
        ity_of_string "(pr -> pr) /\\ (np -> np)"
      );
  ]

let typing_test : test =
  let hg_e, typing_e = mk_typing grammar_e in
  let hg_ax, typing_ax = mk_typing grammar_ax in
  let hg_xyyz, typing_xyyz = mk_typing grammar_xyyz in
  typing_xyyz#add_nt_ty 2 @@ ty_of_string "(pr -> pr) -> (np -> pr) -> np -> pr";
  typing_xyyz#add_nt_ty 3 @@ ty_of_string "(np -> np) -> np -> np";
  init_flags ();
  "typing" >::: [
    "annotate_args" >:: (fun _ ->
        assert_equal
          [
            ([(1, TyList.singleton NP); (2, TyList.singleton PR)], true)
          ]
          (typing_e#annotate_args
             [1; 2]
             (TyList.singleton
                (Fun (2, TyList.singleton NP,
                      Fun (3, TyList.singleton PR,
                           Fun (4, TyList.empty, PR)
                          )
                     )
                )
             )
          )
      );

    "infer_wo_venv-1" >:: (fun _ ->
        assert_equal_venvls
          [VEnv.empty]
          (typing_e#infer_wo_venv (hg_e#find_term (T E)) NP false false)
      );

    "infer_wo_venv-2" >:: (fun _ ->
        assert_equal_venvls
          []
          (typing_e#infer_wo_venv (hg_e#find_term (T E)) NP false true)
      );

    "infer_wo_venv-3" >:: (fun _ ->
        assert_equal_venvls
          [VEnv.empty]
          (typing_e#infer_wo_venv (hg_e#find_term (T E)) NP true false)
      );

    "infer_wo_venv-4" >:: (fun _ ->
        assert_equal_venvls
          [
            VEnv.singleton ((1, 0), sty PR);
            VEnv.singleton ((1, 0), sty NP)
          ]
          (typing_ax#infer_wo_venv (hg_ax#nt_body 1) PR false false)
      );

    "infer_wo_venv-5" >:: (fun _ ->
        assert_equal_venvls
          []
          (typing_ax#infer_wo_venv (hg_ax#nt_body 1) NP false false)
      );

    "infer_wo_venv-6" >:: (fun _ ->
        assert_equal_venvls
          [
            VEnv.of_list [
              ((1, 0), ity_of_string "pr -> pr");
              ((1, 1), ity_of_string "(np -> pr) /\\ (np -> np)");
              ((1, 2), ity_of_string "np")
            ]
          ]
          (typing_xyyz#infer_wo_venv (hg_xyyz#nt_body 1) PR false false)
      );

    "infer_wo_venv-7" >:: (fun _ ->
        assert_equal_venvls
          [
            VEnv.singleton ((4, 0), ity_of_string "pr");
            VEnv.singleton ((4, 0), ity_of_string "np")
          ]
          (typing_xyyz#infer_wo_venv (hg_xyyz#nt_body 4) PR false false)
      );

    "infer_wo_venv-8" >:: (fun _ ->
        assert_equal_venvls
          [
            VEnv.singleton ((4, 0), ity_of_string "pr");
            VEnv.singleton ((4, 0), ity_of_string "np")
          ]
          (typing_xyyz#infer_wo_venv (hg_xyyz#nt_body 4) NP false false)
      );

    (* TODO tests with:
       * filtered out duplication when target is np
       * filtered out no duplication when target is pr and nothing else is pr
       * passed no duplication when target is pr and nothing else is pr
    *)
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
      type_test;
      typing_test;
      (* examples_test *)
    ])
