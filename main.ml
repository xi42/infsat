(*open Utilities*)
(*open Grammar*)
(*open Automaton*)

(** Parses a file to HORS prerules and automata definition. *)
let parseFile filename =
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
let parseStdIn() =
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

exception Profiled

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

let report_breakdown start_t end_t =
  let ts = List.rev !times in
  let last = if !times=[] then start_t else List.hd !times in
  let start = ref start_t in
  List.iter 
  (fun t -> 
    print_string ("  checkpoint: "^(string_of_float (t -. !start))^"sec\n");
    start := t)
  ts;
  print_string ("  checkpoint: "^(string_of_float (end_t -. last))^"sec\n")
*)

exception NotImplemented

(** Prints if HORS specified by prerules is accepted by given automata transitions.
    Takes output of parseFile. *)
(* verifyParseResult : Syntax.prerules * Syntax.transitions -> () *)
let verifyParseResult (prerules,tr) =
  raise NotImplemented
  (*
  match tr with
    | Syntax.Alternating (rs,tr) -> begin
        let (g, m) = Conversion.convert_ata (prerules,rs,tr) in
        (report_input_ata g m;
         let alpha1 = Stype.tcheck g m.AlternatingAutomaton.alpha in 
         Grammar.update_arity alpha1;
         Ai.mk_trtab_for_ata m;
         let m' = AlternatingAutomaton.negate m in
         Type.set_num_of_states(List.length (m.AlternatingAutomaton.st));
         Saturate.ata2cte m';
         if !Flags.debugging then Saturate.print_cte();
         Saturate.mk_linearity_tab();
         check_point();
         Ai.init_expansion 0;
         check_point();
         Ai.expand();
         check_point();
         Ai.mk_binding_depgraph(); (* 3 check_points *)
         check_point();
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

let string_of_parseresult (prerules, tr) =
  (Syntax.string_of_prerules prerules)^"\n"^(Syntax.string_of_preterminals tr)

let suicide() =
  let pid = Unix.getpid() in
    Unix.kill pid Sys.sigabrt 

exception LogFile

let web = ref false

let create_logfile() =
  let n = Unix.time() in
  let prefix = if !web then "/home/koba/horsat/log/log" else "log" in
  let filename = prefix^(string_of_int (int_of_float n))^".hrs" in
  let fp = open_out_gen [Open_wronly;Open_creat;Open_excl;Open_trunc] 0o666 filename in
  (filename, fp)

let write_log parseresult =
  let s = string_of_parseresult parseresult in
  (*let _ = Random.init(int_of_float(Unix.time())) in*)
  let (filename, fp) = create_logfile() in
  let _ = output_string fp s in
    (close_out fp; filename)

let rec loop() = loop()

let report_usage () =
    (print_string "Usage: \n";
     print_string "horsat <option>* <filename> \n\n";
     print_string " -d\n";
     print_string "  debug mode\n";
    )

let rec read_options index =
  match Sys.argv.(index) with
   "-d" -> (Flags.debugging := true; read_options (index+1))
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
  let start_t = Sys.time() in
  let (index,flag) = 
      try
        (read_options 1, true)
      with
        Invalid_argument _ -> (0,false)
      | _ -> 
         (print_string "Invalid options\n\n";
          report_usage();
          exit (-1))
  in
  let parseresult =
    try
      if flag then
         parseFile(Sys.argv.(index))
      else
         parseStdIn()
    with
	InfSatLexer.LexError s -> (print_string ("lex error: "^s^"\n"); exit (-1))
  in
 let _ = if !web then Unix.alarm 3 else 0 in
  let logfile = if !Flags.logging then write_log parseresult else "" in
    ((* Sys.set_signal Sys.sigalrm (Sys.Signal_handle(fun sigid -> write_log (string_of_parseresult parseresult))); *)
      (* loop();*)  (* for testing logging *)
     (try verifyParseResult parseresult with Profiled -> ());
     let end_t = Sys.time() in
       (print_string ("Elapsed Time: "^(string_of_float (end_t -. start_t))^"sec\n");
        (* if !debugging then report_breakdown start_t end_t;*)
        flush stdout;
        if !Flags.logging then Unix.unlink logfile else ())
    )

let () = if !Sys.interactive then () else main()
