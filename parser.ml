type token =
  | NAME of (string)
  | NONTERM of (string)
  | INT of (int)
  | ARROW
  | PERIOD
  | LPAR
  | RPAR
  | BEGING
  | BEGINT
  | END
  | EOF

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
open Syntax
# 19 "parser.ml"
let yytransl_const = [|
  260 (* ARROW *);
  261 (* PERIOD *);
  262 (* LPAR *);
  263 (* RPAR *);
  264 (* BEGING *);
  265 (* BEGINT *);
  266 (* END *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* NAME *);
  258 (* NONTERM *);
  259 (* INT *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\009\000\009\000\003\000\003\000\006\000\006\000\
\006\000\005\000\007\000\007\000\004\000\004\000\008\000\010\000\
\010\000\011\000\011\000\000\000"

let yylen = "\002\000\
\003\000\003\000\001\000\002\000\005\000\004\000\001\000\001\000\
\003\000\001\000\001\000\002\000\001\000\002\000\003\000\001\000\
\002\000\003\000\004\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\020\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\004\000\002\000\000\000\
\000\000\000\000\001\000\014\000\008\000\007\000\000\000\000\000\
\000\000\010\000\000\000\000\000\015\000\017\000\000\000\006\000\
\012\000\000\000\000\000\009\000\005\000\019\000"

let yydgoto = "\002\000\
\004\000\005\000\007\000\013\000\024\000\025\000\026\000\010\000\
\008\000\017\000\018\000"

let yysindex = "\002\000\
\000\255\000\000\008\255\000\000\005\255\003\255\008\255\002\255\
\012\255\015\000\015\255\255\254\013\255\000\000\000\000\014\255\
\009\255\012\255\000\000\000\000\000\000\000\000\255\254\016\255\
\255\254\000\000\255\254\017\255\000\000\000\000\018\255\000\000\
\000\000\019\255\021\255\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\020\255\000\000\
\000\000\000\000\022\255\000\000\000\000\000\000\000\000\000\000\
\000\000\023\255\000\000\000\000\000\000\000\000\000\000\000\000\
\004\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\024\255\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\000\000\012\000\235\255\000\000\003\000\000\000\
\020\000\011\000\000\000"

let yytablesize = 34
let yytable = "\021\000\
\022\000\031\000\001\000\011\000\023\000\034\000\012\000\003\000\
\011\000\006\000\011\000\015\000\016\000\009\000\019\000\011\000\
\027\000\028\000\029\000\035\000\032\000\038\000\020\000\037\000\
\036\000\013\000\014\000\033\000\030\000\003\000\000\000\000\000\
\016\000\018\000"

let yycheck = "\001\001\
\002\001\023\000\001\000\001\001\006\001\027\000\004\001\008\001\
\005\001\002\001\007\001\010\001\001\001\009\001\000\000\001\001\
\004\001\004\001\010\001\003\001\005\001\001\001\011\000\005\001\
\007\001\004\001\007\000\025\000\018\000\010\001\255\255\255\255\
\010\001\010\001"

let yynames_const = "\
  ARROW\000\
  PERIOD\000\
  LPAR\000\
  RPAR\000\
  BEGING\000\
  BEGINT\000\
  END\000\
  EOF\000\
  "

let yynames_block = "\
  NAME\000\
  NONTERM\000\
  INT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Syntax.prerules) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Syntax.preterminals) in
    Obj.repr(
# 31 "parser.mly"
  ((_1, _2))
# 116 "parser.ml"
               : Syntax.prerules * Syntax.preterminals))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'prules) in
    Obj.repr(
# 35 "parser.mly"
  (_2)
# 123 "parser.ml"
               : Syntax.prerules))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Syntax.prerule) in
    Obj.repr(
# 39 "parser.mly"
  ([_1])
# 130 "parser.ml"
               : 'prules))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Syntax.prerule) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'prules) in
    Obj.repr(
# 41 "parser.mly"
  (_1::_2)
# 138 "parser.ml"
               : 'prules))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string list) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Syntax.preterm) in
    Obj.repr(
# 45 "parser.mly"
  ((_1, _2, _4))
# 147 "parser.ml"
               : Syntax.prerule))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Syntax.preterm) in
    Obj.repr(
# 47 "parser.mly"
  ((_1, [], _3))
# 155 "parser.ml"
               : Syntax.prerule))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 51 "parser.mly"
  (PApp(NT(_1), []))
# 162 "parser.ml"
               : Syntax.preterm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 53 "parser.mly"
  (PApp(Name(_1), []))
# 169 "parser.ml"
               : Syntax.preterm))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Syntax.preterm) in
    Obj.repr(
# 55 "parser.mly"
  (_2)
# 176 "parser.ml"
               : Syntax.preterm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Syntax.preterm list) in
    Obj.repr(
# 59 "parser.mly"
  (match _1 with
   | [x] -> x
   | PApp(h, [])::terms -> PApp(h, terms)
   | _ -> assert false)
# 186 "parser.ml"
               : Syntax.preterm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Syntax.preterm) in
    Obj.repr(
# 66 "parser.mly"
  ([_1])
# 193 "parser.ml"
               : Syntax.preterm list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Syntax.preterm) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Syntax.preterm list) in
    Obj.repr(
# 68 "parser.mly"
  (_1::_2)
# 201 "parser.ml"
               : Syntax.preterm list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 72 "parser.mly"
  ([_1])
# 208 "parser.ml"
               : string list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string list) in
    Obj.repr(
# 74 "parser.mly"
  (_1::_2)
# 216 "parser.ml"
               : string list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'pterminals) in
    Obj.repr(
# 78 "parser.mly"
  (_2)
# 223 "parser.ml"
               : Syntax.preterminals))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'terminal) in
    Obj.repr(
# 82 "parser.mly"
  ([_1])
# 230 "parser.ml"
               : 'pterminals))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'terminal) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'pterminals) in
    Obj.repr(
# 84 "parser.mly"
  (_1::_2)
# 238 "parser.ml"
               : 'pterminals))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 88 "parser.mly"
  (PTerminal(_1, _3, false))
# 246 "parser.ml"
               : 'terminal))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 90 "parser.mly"
  (match _4 with
   | "counted" -> PTerminal(_1, _3, true)
   | _ -> assert false)
# 257 "parser.ml"
               : 'terminal))
(* Entry main *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let main (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Syntax.prerules * Syntax.preterminals)
