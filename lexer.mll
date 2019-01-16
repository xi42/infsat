{
open Parser
exception LexError of string
let line_no = ref 1
let end_of_previousline = ref 0
}

let space = [' ' '\t' '\r']
let newline = ['\n']
let digit = ['0'-'9']
let lower = ['a'-'z']
let upper = ['A'-'Z']

rule token = parse
| space+
    { token lexbuf }
| newline
    { end_of_previousline := (Lexing.lexeme_end lexbuf);
      line_no := !line_no+1;
      token lexbuf}
| "(*"
    { comment lexbuf;
      token lexbuf }
| digit digit* 
   {let s = Lexing.lexeme lexbuf in
     INT(int_of_string s)}
| lower (digit|lower|upper|'_')*
    { let s = Lexing.lexeme lexbuf in
         NAME(s)}
| upper (digit|lower|upper|'_')*
    { let s = Lexing.lexeme lexbuf in
        NONTERM(s)}
| "Grammar."
    {BEGING}
| "End."
    {END}
| "Terminals."
    {BEGINT}
| "->"
    {ARROW}
| "("
    {LPAR}
| ")"
    {RPAR}
| "."
    {PERIOD}
| eof
    { EOF }
| _
    { Format.eprintf "unknown token %s in line %d, column %d-%d @."
	(Lexing.lexeme lexbuf)
        (!line_no)
	((Lexing.lexeme_start lexbuf)- (!end_of_previousline))
	((Lexing.lexeme_end lexbuf)-(!end_of_previousline));
      failwith "lex error" }
and comment = parse
| "*)"
    { () }
| "(*"
    { comment lexbuf;
      comment lexbuf }
| eof
    {  print_string "Lex error: unterminated comment\n";
       failwith "unterminated comment" }
| _
    { comment lexbuf }
