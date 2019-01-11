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

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Syntax.prerules * Syntax.automaton
