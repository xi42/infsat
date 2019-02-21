open Binding
open Environment
open Grammar
open GrammarCommon
open HGrammar
open HtyStore
open Main
open OUnit2
open Type
open Typing
open Utilities

(* --- helper functions --- *)

let init_flags () =
  Flags.debugging := true;
  Flags.verbose := !Flags.debugging

let assert_equal_envls envl1 envl2 =
  assert_equal ~printer:string_of_envl (sort_envl envl1) (sort_envl envl2)

let mk_grammar rules =
  let nonterminals = Array.mapi (fun i _ -> ("N" ^ string_of_int i, O)) rules in
  let g = new grammar nonterminals [||] rules in
  print_string "Creating grammar:\n";
  g#print_gram;
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

(* --- tests --- *)

let type_test () : test =
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

(** The smallest possible grammar. *)
let grammar_e () = mk_grammar
    [|
      (0, T E); (* N0 -> e *)
    |]

let typing_e_test () =
  let hg, typing = mk_typing @@ grammar_e () in
  [
    (* checking if matching arguments to their types works *)
    "annotate_args" >:: (fun _ ->
        assert_equal
          [
            ([(1, TyList.singleton NP); (2, TyList.singleton PR)], true)
          ]
          (typing#annotate_args
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
    
    (* check if e : np type checks *)
    "infer_wo_env-1" >:: (fun _ ->
        assert_equal_envls
          [Env.empty]
          (typing#infer_wo_env (hg#find_term (T E)) NP false false)
      );

    (* checking basic functionality of forcing pr vars *)
    "infer_wo_env-2" >:: (fun _ ->
        assert_equal_envls
          []
          (typing#infer_wo_env (hg#find_term (T E)) NP false true)
      );

    (* checking that forcing no pr vars does not break anything when there are only terminals *)
    "infer_wo_env-3" >:: (fun _ ->
        assert_equal_envls
          [Env.empty]
          (typing#infer_wo_env (hg#find_term (T E)) NP true false)
      );
  ]

(** Grammar that tests usage of a variable. *)
let grammar_ax () = mk_grammar
    [|
      (0, App (NT 1, T E)); (* N0 -> N1 e *)
      (1, App (T A, Var (1, 0))); (* N1 x -> a x *)
    |]

let typing_ax_test () =
  let hg, typing = mk_typing @@ grammar_ax () in
  (* check that a x : pr accepts both productivities of x *)
  [
    "infer_wo_env-4" >:: (fun _ ->
        assert_equal_envls
          [
            Env.singleton ((1, 0), sty PR);
            Env.singleton ((1, 0), sty NP)
          ]
          (typing#infer_wo_env (hg#nt_body 1) PR false false)
      );

    (* check that a x : np does not type check *)
    "infer_wo_env-5" >:: (fun _ ->
        assert_equal_envls
          []
          (typing#infer_wo_env (hg#nt_body 1) NP false false)
      );
  ]
  
(** Grammar that tests intersection - x and y are inferred from one argument in N1 rule, and y and
    z from the other. N4 tests top. *)
let grammar_xyyz () = mk_grammar
    [|
      (* N0 -> N1 a N4 e *)
      (0, App (App (App (NT 1, T A), NT 4), T E));
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
      (1, App (App (T B, App (T A, Var (4, 0))), Var (4, 0)));
      (* N5 -> N5 *)
      (0, NT 5);
    |]

let typing_xyyz_test () =
  let hg, typing = mk_typing @@ grammar_xyyz () in
  typing#add_nt_ty 2 @@ ty_of_string "(pr -> pr) -> (np -> pr) -> np -> pr";
  typing#add_nt_ty 3 @@ ty_of_string "(np -> np) -> np -> np";
  let id1 = hg#locate_hterms_id 0 [0] in
  typing#get_htys#add_hty id1
    [
      ity_of_string "pr -> pr";
      ity_of_string "np -> np";
      ity_of_string "np -> pr";
    ];
  typing#get_htys#add_hty id1
    [
      ity_of_string "pr -> pr";
      ity_of_string "pr -> pr";
      ity_of_string "pr -> pr";
    ];
  [
    (* check that intersection of common types from different arguments works *)
    "infer_wo_env-6" >:: (fun _ ->
        assert_equal_envls
          [
            Env.of_list [
              ((1, 0), ity_of_string "pr -> pr");
              ((1, 1), ity_of_string "(np -> pr) /\\ (np -> np)");
              ((1, 2), ity_of_string "np")
            ]
          ]
          (typing#infer_wo_env (hg#nt_body 1) PR false false)
      );

    (* check that branching works *)
    "infer_wo_env-7" >:: (fun _ ->
        assert_equal_envls
          [
            Env.singleton ((4, 0), ity_of_string "pr");
            Env.singleton ((4, 0), ity_of_string "np")
          ]
          (typing#infer_wo_env (hg#nt_body 4) PR false false)
      );

    (* check that branching works *)
    "infer_wo_env-8" >:: (fun _ ->
        assert_equal_envls
          [
            Env.singleton ((4, 0), ity_of_string "pr");
            Env.singleton ((4, 0), ity_of_string "np")
          ]
          (typing#infer_wo_env (hg#nt_body 4) NP false false)
      );

    "mk_hty_bindings" >:: (fun _ ->
        assert_equal
          [
            [(0, 0,
              [
                ity_of_string "pr -> pr";
                ity_of_string "pr -> pr";
                ity_of_string "pr -> pr";
              ]
             )];
            [(0, 0,
              [
                ity_of_string "pr -> pr";
                ity_of_string "np -> np";
                ity_of_string "np -> pr";
              ]
             )];
          ]
          (List.sort (binding_compare hty_compare) @@ typing#mk_hty_bindings [(0, 0, id1)])
      );
  ]

(** Grammar that tests typing with duplication in N1 when N2 receives two the same arguments. It
    also tests no duplication when these arguments are different in N3. *)
let grammar_dup () = mk_grammar
    [|
      (* N0 -> b (b (N1 a) (N3 a a)) (N4 a a (a e)) *)
      (0, App (App (
           T B,
           App (App (
               T B,
               App (NT 2, T A)),
                App (App (NT 3, T A), App (T A, T E)))),
               App (App (App (NT 4, T A), T A), App (T A, T E))));
      (* N1 x y z -> x (y z) *)
      (3, App (Var (1, 0), App  (Var (1, 1), Var (1, 2))));
      (* N2 x -> N1 x x (a e) *)
      (1, App (App (App (NT 1, Var (2, 0)), Var (2, 0)), App (T A, T E)));
      (* N3 x y -> N1 x x y *)
      (2, App (App (App (NT 1, Var (3, 0)), Var (3, 0)), Var (3, 1)));
      (* N4 x y z -> N1 x y z *)
      (3, App (App (App (NT 1, Var (4, 0)), Var (4, 1)), Var (4, 2)));
    |]

let typing_dup_test () =
  let hg, typing = mk_typing @@ grammar_dup () in
  typing#add_nt_ty 1 @@ ty_of_string  "(pr -> pr) -> (pr -> pr) -> pr -> np";
  typing#add_nt_ty 1 @@ ty_of_string  "(pr -> np) -> (pr -> np) -> pr -> np";
  [
    (* All valid typings of x type check, because the application is already productive due to
       a e being productive. *)
    "infer_wo_env-9" >:: (fun _ ->
        assert_equal_envls
          [
            Env.singleton ((2, 0), ity_of_string "pr -> pr");
            Env.singleton ((2, 0), ity_of_string "pr -> np");
          ]
          (typing#infer_wo_env (hg#nt_body 2) PR false false)
      );

    (* No valid environment, because a e is productive and makes the application with it as
       argument productive. *)
    "infer_wo_env-10" >:: (fun _ ->
        assert_equal_envls
          []
          (typing#infer_wo_env (hg#nt_body 2) NP false false)
      );

    (* Only one valid env when there is a duplication. Since everything in N1 is a variable,
       there is no way to create pr terms without a duplication. The x : pr -> pr typing
       causes a duplication and type checks. Typing x : pr -> np does not type check, because
       it is not productive, so it is not a duplication. y : pr is forced by there being no
       known typing of the head with unproductive last argument.

         * one where a env did not go through because it did not generate a duplication
           (target pr, head np, pr target args, np actual args as different pr vars) *)
    "infer_wo_env-11" >:: (fun _ ->
        assert_equal_envls
          [
            Env.of_list [((3, 0), ity_of_string "pr -> pr"); ((3, 1), ity_of_string "pr")];
          ]
          (typing#infer_wo_env (hg#nt_body 3) PR false false)
      );

    (* Only one valid env when there is no duplication. This is exactly the opposite of the test
       above with x : pr -> np passing and x : pr -> pr failing and y : pr being forced. *)
    "infer_wo_env-12" >:: (fun _ ->
        assert_equal_envls
          [
            Env.of_list [((3, 0), ity_of_string "pr -> np"); ((3, 1), ity_of_string "pr")];
          ]
          (typing#infer_wo_env (hg#nt_body 3) NP false false)
      );

    (* Similar to test 11, but this time there are separate variables used for first
       and second argument, so there is no place for duplication. This means that there is no
       way to achieve productivity. *)
    "infer_wo_env-13" >:: (fun _ ->
        assert_equal_envls
          []
          (typing#infer_wo_env (hg#nt_body 4) PR false false)
      );

    (* Similar to test 12, but this time the duplication cannot happen. *)
    "infer_wo_env-14" >:: (fun _ ->
        assert_equal_envls
          [
            Env.of_list [
              ((4, 0), ity_of_string "pr -> pr");
              ((4, 1), ity_of_string "pr -> pr");
              ((4, 2), ity_of_string "pr");
            ];
            Env.of_list [
              ((4, 0), ity_of_string "pr -> np");
              ((4, 1), ity_of_string "pr -> np");
              ((4, 2), ity_of_string "pr");
            ];
          ]
          (typing#infer_wo_env (hg#nt_body 4) NP false false)
      );
  ]

let typing_test () : test =
  init_flags ();
  "typing" >:::
  typing_e_test () @
  typing_ax_test () @
  typing_xyyz_test () @
  typing_dup_test ()

let cfa_test () : test =
  init_flags ();
  let g = grammar_xyyz () in
  let hg = mk_hgrammar g in
  let cfa = mk_cfa g @@ Some hg in
  "cfa" >:::
  [
    (* empty binding with no variables *)
    "nt_binding-1" >:: (fun _ ->
        assert_equal
          [[]]
          (cfa#lookup_bindings_for_nt 0)
      );

    (* single binding, directly *)
    "nt_binding-2" >:: (fun _ ->
        assert_equal
          [
            [(0, 2, List.hd @@ snd @@ hg#nt_body 0)]
          ]
          (cfa#lookup_bindings_for_nt 1)
      );

    (* two bindings, both indirectly due to partial application *)
    "nt_binding-3" >:: (fun _ ->
        assert_equal
          [
            "nt2v2";
            "nt3v1";
          ]
          (List.sort Pervasives.compare @@ List.map (fun binding ->
               match binding with
               | [(_, _, id)] -> String.concat ", " @@ List.map g#string_of_term @@ hg#id2terms id
               | _ -> failwith "fail"
             ) @@ cfa#lookup_bindings_for_nt 4)
      );

    (* no bindings when unreachable *)
    "nt_binding-4" >:: (fun _ ->
        assert_equal
          []
          (cfa#lookup_bindings_for_nt 5)
      );

    (* checking that cfa detected that in N0 nonterminal N1 was applied to N4 *)
    "var_binding-1" >:: (fun _ ->
        assert_equal
          [
            (HNT 4, []);
          ]
          (cfa#lookup_binding_var (1, 1))
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
            assert_equal (Main.parse_and_report_finiteness (path filename)) false))
      inf_filenames;
    "Finite examples" >::: List.map (fun filename ->
        filename >:: (fun _ ->
            assert_equal (Main.parse_and_report_finiteness (path filename)) true))
      fin_filenames]

let tests () = [
  cfa_test ();
  type_test ();
  typing_test ();
  (* examples_test () *)
]
