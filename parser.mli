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

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Syntax.prerules * Syntax.preterminals
