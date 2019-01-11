type token =
  | NAME of (string)
  | NONTERM of (string)
  | INT of (int)
  | CASE
  | FUN
  | COMMA
  | DP
  | ARROW
  | PERIOD
  | LPAR
  | RPAR
  | LBRA
  | RBRA
  | AND
  | OR
  | BEGING
  | ENDG
  | BEGINA
  | ENDA
  | BEGINR
  | ENDR
  | ML of (string)
  | EOF
  | BEGINATA
  | ENDATA

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
open Syntax
# 33 "parser.ml"
let yytransl_const = [|
  260 (* CASE *);
  261 (* FUN *);
  262 (* COMMA *);
  263 (* DP *);
  264 (* ARROW *);
  265 (* PERIOD *);
  266 (* LPAR *);
  267 (* RPAR *);
  268 (* LBRA *);
  269 (* RBRA *);
  270 (* AND *);
  271 (* OR *);
  272 (* BEGING *);
  273 (* ENDG *);
  274 (* BEGINA *);
  275 (* ENDA *);
  276 (* BEGINR *);
  277 (* ENDR *);
    0 (* EOF *);
  279 (* BEGINATA *);
  280 (* ENDATA *);
    0|]

let yytransl_block = [|
  257 (* NAME *);
  258 (* NONTERM *);
  259 (* INT *);
  278 (* ML *);
    0|]

let yylhs = "\255\255\
\001\000\011\000\002\000\002\000\003\000\003\000\006\000\006\000\
\006\000\006\000\006\000\005\000\005\000\005\000\005\000\007\000\
\007\000\004\000\004\000\012\000\012\000\008\000\008\000\009\000\
\009\000\014\000\014\000\015\000\010\000\010\000\010\000\010\000\
\010\000\013\000\013\000\016\000\000\000"

let yylen = "\002\000\
\003\000\003\000\001\000\002\000\005\000\004\000\001\000\001\000\
\003\000\005\000\001\000\001\000\004\000\004\000\003\000\001\000\
\002\000\001\000\002\000\003\000\006\000\001\000\002\000\004\000\
\005\000\001\000\002\000\005\000\001\000\005\000\003\000\003\000\
\003\000\001\000\002\000\004\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\037\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\002\000\004\000\
\000\000\000\000\000\000\000\000\000\000\000\000\001\000\019\000\
\008\000\007\000\011\000\000\000\000\000\000\000\000\000\000\000\
\000\000\012\000\000\000\000\000\020\000\023\000\000\000\000\000\
\035\000\000\000\000\000\000\000\000\000\006\000\017\000\000\000\
\000\000\000\000\000\000\000\000\000\000\015\000\000\000\009\000\
\005\000\024\000\000\000\036\000\000\000\000\000\000\000\013\000\
\014\000\000\000\025\000\000\000\021\000\027\000\010\000\000\000\
\029\000\000\000\000\000\000\000\000\000\028\000\000\000\000\000\
\000\000\033\000\031\000\000\000\000\000\030\000"

let yydgoto = "\002\000\
\004\000\007\000\008\000\014\000\032\000\033\000\034\000\018\000\
\019\000\075\000\005\000\011\000\021\000\062\000\063\000\022\000"

let yysindex = "\003\000\
\002\255\000\000\020\255\000\000\039\255\023\255\017\255\020\255\
\042\255\047\255\058\000\059\255\025\255\053\255\000\000\000\000\
\061\255\044\255\042\255\056\255\046\255\047\255\000\000\000\000\
\000\000\000\000\000\000\062\255\059\255\006\255\025\255\057\255\
\006\255\000\000\025\255\060\255\000\000\000\000\066\255\048\255\
\000\000\006\255\064\255\006\255\030\255\000\000\000\000\065\255\
\005\255\067\255\069\255\006\255\025\255\000\000\025\255\000\000\
\000\000\000\000\068\255\000\000\072\255\051\255\069\255\000\000\
\000\000\070\255\000\000\071\255\000\000\000\000\000\000\010\255\
\000\000\009\255\024\255\074\255\041\255\000\000\010\255\010\255\
\077\255\000\000\000\000\073\255\075\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\076\255\
\000\000\000\000\000\000\045\255\000\000\000\000\000\000\000\000\
\000\000\000\000\063\255\000\000\000\000\078\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\038\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\079\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\031\255\000\000\000\000"

let yygindex = "\000\000\
\000\000\075\000\000\000\244\255\226\255\229\255\225\255\065\000\
\000\000\227\255\000\000\000\000\063\000\025\000\000\000\000\000"

let yytablesize = 103
let yytable = "\024\000\
\045\000\047\000\044\000\001\000\048\000\012\000\025\000\026\000\
\027\000\073\000\073\000\076\000\054\000\058\000\052\000\031\000\
\043\000\003\000\074\000\074\000\064\000\006\000\065\000\012\000\
\066\000\025\000\026\000\027\000\028\000\029\000\013\000\030\000\
\078\000\015\000\031\000\055\000\059\000\079\000\080\000\032\000\
\056\000\032\000\017\000\016\000\077\000\032\000\016\000\020\000\
\016\000\083\000\084\000\082\000\018\000\018\000\079\000\080\000\
\009\000\023\000\010\000\012\000\035\000\036\000\037\000\039\000\
\042\000\046\000\040\000\049\000\050\000\061\000\051\000\053\000\
\068\000\057\000\069\000\060\000\067\000\085\000\072\000\081\000\
\071\000\022\000\016\000\038\000\041\000\086\000\079\000\070\000\
\000\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\
\000\000\000\000\034\000\000\000\000\000\000\000\026\000"

let yycheck = "\012\000\
\031\000\033\000\030\000\001\000\035\000\001\001\001\001\002\001\
\003\001\001\001\001\001\003\001\044\000\009\001\042\000\010\001\
\029\000\016\001\010\001\010\001\052\000\002\001\053\000\001\001\
\055\000\001\001\002\001\003\001\004\001\005\001\008\001\007\001\
\009\001\017\001\010\001\006\001\049\000\014\001\015\001\009\001\
\011\001\011\001\001\001\006\001\074\000\015\001\009\001\001\001\
\011\001\079\000\080\000\011\001\008\001\009\001\014\001\015\001\
\018\001\000\000\020\001\001\001\008\001\001\001\019\001\008\001\
\003\001\009\001\021\001\008\001\003\001\001\001\023\001\008\001\
\001\001\009\001\024\001\009\001\009\001\001\001\008\001\006\001\
\011\001\019\001\008\000\019\000\022\000\011\001\014\001\063\000\
\255\255\255\255\255\255\255\255\017\001\255\255\255\255\255\255\
\255\255\255\255\021\001\255\255\255\255\255\255\024\001"

let yynames_const = "\
  CASE\000\
  FUN\000\
  COMMA\000\
  DP\000\
  ARROW\000\
  PERIOD\000\
  LPAR\000\
  RPAR\000\
  LBRA\000\
  RBRA\000\
  AND\000\
  OR\000\
  BEGING\000\
  ENDG\000\
  BEGINA\000\
  ENDA\000\
  BEGINR\000\
  ENDR\000\
  EOF\000\
  BEGINATA\000\
  ENDATA\000\
  "

let yynames_block = "\
  NAME\000\
  NONTERM\000\
  INT\000\
  ML\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'gram) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'automaton) in
    Obj.repr(
# 49 "parser.mly"
  ( (_1, _2)  )
# 196 "parser.ml"
               : Syntax.prerules * Syntax.automaton))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Syntax.prerules) in
    Obj.repr(
# 53 "parser.mly"
  (_2)
# 203 "parser.ml"
               : 'gram))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Syntax.prerule) in
    Obj.repr(
# 57 "parser.mly"
   ([_1])
# 210 "parser.ml"
               : Syntax.prerules))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Syntax.prerule) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Syntax.prerules) in
    Obj.repr(
# 59 "parser.mly"
   (_1::_2)
# 218 "parser.ml"
               : Syntax.prerules))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string list) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Syntax.preterm) in
    Obj.repr(
# 63 "parser.mly"
  ((_1, _2, _4))
# 227 "parser.ml"
               : Syntax.prerule))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Syntax.preterm) in
    Obj.repr(
# 66 "parser.mly"
  ((_1, [], _3))
# 235 "parser.ml"
               : Syntax.prerule))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 70 "parser.mly"
  (PTapp(NT(_1), []))
# 242 "parser.ml"
               : Syntax.preterm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 72 "parser.mly"
  (PTapp(Name(_1),[]))
# 249 "parser.ml"
               : Syntax.preterm))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Syntax.preterm) in
    Obj.repr(
# 74 "parser.mly"
  (_2)
# 256 "parser.ml"
               : Syntax.preterm))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Syntax.preterm) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Syntax.preterm) in
    Obj.repr(
# 76 "parser.mly"
  (PTapp(PAIR, [_2; _4]))
# 264 "parser.ml"
               : Syntax.preterm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 78 "parser.mly"
  (PTapp(FD(_1), []))
# 271 "parser.ml"
               : Syntax.preterm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Syntax.preterm list) in
    Obj.repr(
# 82 "parser.mly"
  (match _1 with
     [] -> assert false
   | [x] -> x
   | x::terms ->
      match x with
        PTapp(h,l) -> PTapp(h, l@terms))
# 283 "parser.ml"
               : Syntax.preterm))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Syntax.preterm) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Syntax.preterm list) in
    Obj.repr(
# 89 "parser.mly"
  (PTapp(CASE(_2), _3::_4))
# 292 "parser.ml"
               : Syntax.preterm))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string list) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Syntax.preterm) in
    Obj.repr(
# 91 "parser.mly"
  (PTapp(FUN(_2, _4), []))
# 300 "parser.ml"
               : Syntax.preterm))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Syntax.preterm) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Syntax.preterm list) in
    Obj.repr(
# 93 "parser.mly"
  (PTapp(DPAIR, _2::_3))
# 308 "parser.ml"
               : Syntax.preterm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Syntax.preterm) in
    Obj.repr(
# 97 "parser.mly"
  ([_1])
# 315 "parser.ml"
               : Syntax.preterm list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Syntax.preterm) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Syntax.preterm list) in
    Obj.repr(
# 99 "parser.mly"
  (_1::_2)
# 323 "parser.ml"
               : Syntax.preterm list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 103 "parser.mly"
  ([_1])
# 330 "parser.ml"
               : string list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string list) in
    Obj.repr(
# 105 "parser.mly"
  (_1::_2)
# 338 "parser.ml"
               : string list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Syntax.transitions) in
    Obj.repr(
# 109 "parser.mly"
                             ( Trivial(_2) )
# 345 "parser.ml"
               : 'automaton))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'ranks) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'ata_rules) in
    Obj.repr(
# 110 "parser.mly"
                                                 ( Alternating (_2,_5) )
# 353 "parser.ml"
               : 'automaton))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Syntax.transition) in
    Obj.repr(
# 114 "parser.mly"
  ([_1])
# 360 "parser.ml"
               : Syntax.transitions))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Syntax.transition) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Syntax.transitions) in
    Obj.repr(
# 116 "parser.mly"
  (_1::_2)
# 368 "parser.ml"
               : Syntax.transitions))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 121 "parser.mly"
 (((_1, _2), []))
# 376 "parser.ml"
               : Syntax.transition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : string list) in
    Obj.repr(
# 123 "parser.mly"
 (((_1, _2), _4))
# 385 "parser.ml"
               : Syntax.transition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'ata_rule) in
    Obj.repr(
# 127 "parser.mly"
              ([_1])
# 392 "parser.ml"
               : 'ata_rules))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'ata_rule) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'ata_rules) in
    Obj.repr(
# 128 "parser.mly"
                        (_1::_2)
# 400 "parser.ml"
               : 'ata_rules))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Syntax.preformula) in
    Obj.repr(
# 132 "parser.mly"
                                     ( (_1, _2), _4 )
# 409 "parser.ml"
               : 'ata_rule))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 136 "parser.mly"
          ( FConst(_1) )
# 416 "parser.ml"
               : Syntax.preformula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 137 "parser.mly"
                              ( FVar (_2,_4) )
# 424 "parser.ml"
               : Syntax.preformula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Syntax.preformula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Syntax.preformula) in
    Obj.repr(
# 138 "parser.mly"
                                 ( FAnd (_1,_3) )
# 432 "parser.ml"
               : Syntax.preformula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Syntax.preformula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Syntax.preformula) in
    Obj.repr(
# 139 "parser.mly"
                                 ( FOr  (_1,_3) )
# 440 "parser.ml"
               : Syntax.preformula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Syntax.preformula) in
    Obj.repr(
# 140 "parser.mly"
                             ( _2 )
# 447 "parser.ml"
               : Syntax.preformula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'rank) in
    Obj.repr(
# 144 "parser.mly"
          ( [_1] )
# 454 "parser.ml"
               : 'ranks))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'rank) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'ranks) in
    Obj.repr(
# 145 "parser.mly"
                ( _1::_2)
# 462 "parser.ml"
               : 'ranks))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 149 "parser.mly"
                        ( (_1,_3) )
# 470 "parser.ml"
               : 'rank))
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
   (Parsing.yyparse yytables 1 lexfun lexbuf : Syntax.prerules * Syntax.automaton)
