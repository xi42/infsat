open Profiling
open Utilities
(*open Grammar*)
(*open Automaton*)

(** Parses a file to HORS prerules and automata definition. *)
let parse_file filename =
  let in_strm = 
    try
      open_in filename 
    with
	Sys_error _ -> (print_string ("Cannot open file: "^filename^"\n");exit(-1)) in
  let _ = print_string ("analyzing "^filename^"...\n") in
  let _ = flush stdout in
  let lexbuf = Lexing.from_channel in_strm in
  let result =
    try
      InfSatParser.main InfSatLexer.token lexbuf
    with 
	Failure _ -> exit(-1) (*** exception raised by the lexical analyer ***)
      | Parsing.Parse_error -> (print_string "Parse error\n";exit(-1)) in
  let _ = 
    try
      close_in in_strm
    with
	Sys_error _ -> (print_string ("Cannot close file: "^filename^"\n");exit(-1)) 
  in
    result

(** Parses stdin to HORS prerules and automata transitions. *)
let parse_stdin() =
  let _ = print_string ("reading standard input ...\n") in
  let in_strm = stdin in
  let lexbuf = Lexing.from_channel in_strm in
  let result =
    try
      InfSatParser.main InfSatLexer.token lexbuf
    with 
	Failure _ -> exit(-1) (*** exception raised by the lexical analyer ***)
      | Parsing.Parse_error -> (print_string "Parse error\n";exit(-1)) 
  in
    result

(*
let rec report_input g m =
  let _ = if !(Flags.debugging) then print_gram g in
  let _ = print_string ("The number of rewrite rules: "^(string_of_int (Array.length g.r))^"\n") in
  let _ = print_string ("The size of recursion scheme: "^(string_of_int (Grammar.size_of g))^"\n") in
  let _ = print_string ("The number of states: "^(string_of_int (Automaton.size_st m))^"\n") in
    ()

let report_input_ata g m = 
  let r = Array.length g.r in
  let s = Grammar.size_of g in
  let q = List.length m.AlternatingAutomaton.st in
  let _ = if !(Flags.debugging) then print_gram g in
  let str = 
    "The number of rewrite rules: "^(string_of_int r)^"\n" ^
    "The size of recursion scheme: "^(string_of_int s)^"\n" ^
    "The number of states: "^(string_of_int q)^"\n" in
  print_string str
*)

(** Main part of InfSat. Takes parsed input, computes if the language contains
    arbitrarily many counted letters. Prints the result. *)
let report_finiteness input =
  profile "conversion" (fun () -> Conversion.prerules2gram input);
  profile "eta-expansion" (fun () -> Stype.eta_expand());
  profile "0CFA" (fun () -> Cfa.init_expansion(); Cfa.expand());
  profile "dependency graph" (fun () -> Cfa.mk_binding_depgraph());
  ()
  (* TODO
  match tr with
    | Syntax.Alternating (rs,tr) -> begin
DONE    let (g, m) = Conversion.convert_ata (prerules,rs,tr) in
DONE     (report_input_ata g m;
DONE     let alpha1 = Stype.tcheck g m.AlternatingAutomaton.alpha in 
SKIP     Grammar.update_arity alpha1;
SKIP     Ai.mk_trtab_for_ata m;
SKIP     let m' = AlternatingAutomaton.negate m in
SKIP     Type.set_num_of_states(List.length (m.AlternatingAutomaton.st));
SKIP     Saturate.ata2cte m';
SKIP     if !Flags.debugging then Saturate.print_cte();
SKIP     Saturate.mk_linearity_tab();
DONE     check_point();
DONE     Ai.init_expansion 0;
DONE     check_point();
DONE     Ai.expand();
DONE     check_point();
DONE     Ai.mk_binding_depgraph(); (* 3 check_points *)
DONE     check_point();
         Saturate.saturate() (* 2 check_points *)
        )
(*        verify_ata g m *)
    end
    | Syntax.Trivial tr -> begin
      Flags.dautomaton := true;
      let (g, m) = Conversion.convert (prerules,tr) in (* note that the grammar is then stored in Grammar.gram *)
      (report_input g m; (* print info *)
       check_point(); (* save timestamp *)
        let alpha1 = Stype.tcheck g m.alpha in
         check_point();
        let m' = {alpha=alpha1;st=m.st;delta=m.delta;init=m.init} in
        ( Grammar.update_arity alpha1; (* updates arity alone in Grammar.gram to one computed in tcheck *)
         Ai.mk_trtab m';
         check_point();
          Type.set_num_of_states(List.length m.st); (* write to Type.num_of_states how many states there are *)
         Saturate.automaton2cte m';
         if !Flags.debugging then Saturate.print_cte();
         Saturate.mk_linearity_tab();
         check_point();
         Ai.init_expansion 0;
         check_point();
         Ai.expand();
         check_point();
         Ai.mk_binding_depgraph();
         check_point();
         Saturate.saturate()))
(*        verify g m  *)
    end
*)

let string_of_input (prerules, tr) =
  (Syntax.string_of_prerules prerules)^"\n"^(Syntax.string_of_preterminals tr)

let report_usage () =
    (print_string "Usage: \n";
     print_string "infsat <option>* <filename> \n\n";
     print_string " -d\n";
     print_string "  debug mode\n";
    )

let rec read_options index =
  match Sys.argv.(index) with
  | "-d" -> (Flags.debugging := true; read_options (index+1))
  | "-noce" -> (Flags.ce := false; read_options (index+1))
  | "-subt" -> (Flags.subty := true; read_options (index+1))
  | "-o" -> (Flags.outputfile := Sys.argv.(index+1); read_options (index+2))
  | "-r" -> (Flags.redstep := int_of_string(Sys.argv.(index+1));
             Flags.flow := false;
             read_options(index+2))
  | "-n" -> (Flags.normalize := true;
             Flags.normalization_depth := int_of_string(Sys.argv.(index+1));
             read_options(index+2))
  | "-lazy" -> (Flags.eager := false;
			      read_options(index+1))
  | "-merge" -> (Flags.merge_vte := true;
			      read_options(index+1))
  | "-nn" -> (Flags.normalize := false;
			      read_options(index+1))
  | "-tyterm2" -> (Flags.ty_of_term := true;read_options(index+1))
  | "-c" -> (Flags.compute_alltypes := true;read_options (index+1))
  | "-noinc" -> (Flags.incremental := false;read_options (index+1))
  | "-nooverwrite" -> (Flags.overwrite := false;read_options (index+1))
  | "-subty" -> (Flags.subtype_hash := true;read_options (index+1))
  | "-nosubty" -> (Flags.nosubtype := true;read_options (index+1))
  | "-ne" -> (Flags.emptiness_check := false; read_options (index+1))
  | "-bdd" -> (Flags.bdd_mode := 1; read_options (index+1))
  | "-bdd2" -> (Flags.bdd_mode := 2; read_options (index+1))
  | "-prof" -> (Flags.profile := true; read_options (index+1))
  | "-flowcts" -> (Flags.add_flow_cts := true; read_options (index+1))
  | "-notenv" -> (Flags.report_type_env := false; read_options (index+1))
  | "-v" -> (Flags.verbose := true; read_options (index+1))
  | "-cert" -> (Flags.certificate := true; read_options (index+1))
  | _ -> index

let main () =
  let _ = print_string "InfSat2 0.1: Saturation-based finiteness checker for higher-order recursion schemes\n" in
  flush stdout;
  let start_t = Sys.time() in
  let (index,interactive) = 
    try
      (read_options 1, false)
    with
    | Invalid_argument _ -> (0, true)
    | _ -> 
      (print_string "Invalid options\n\n";
       report_usage();
       exit (-1))
  in
  let input = profile "parsing" (fun () ->
      try
        if interactive then
          parse_stdin()
        else
          parse_file(Sys.argv.(index))
      with
        InfSatLexer.LexError s -> (print_string ("Lexer error: "^s^"\n"); exit (-1))
    )
  in
  if !Flags.debugging then
    print_string ("Input:\n"^(string_of_input input)^"\n");
  (* the main part *)
  report_finiteness input;
  let end_t = Sys.time() in report_timings start_t end_t;
  flush stdout

let () = if !Sys.interactive then () else main()
