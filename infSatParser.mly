%{
open Syntax
%}

%token <string> NAME
%token <string> NONTERM
%token <int> INT
%token COUNTED
%token ARROW
%token FUN
%token PERIOD
%token LPAR
%token RPAR
%token BEGING
%token BEGINT
%token END
%token EOF

%start main
%type <Syntax.prerules * Syntax.preterminals> main
%type <Syntax.prerules> rules
%type <Syntax.prerule> rule
%type <string list> names
%type <Syntax.preterm> term
%type <Syntax.preterm> subterm
%type <Syntax.preterm list> terms_list
%type <Syntax.preterminals> terminals

%%

main:
  rules terminals EOF
  {($1, $2)};

rules:
  BEGING rules_list END
  {$2};

rules_list:
| rule 
  {[$1]}
| rule rules_list
  {$1::$2};

rule:
| NONTERM names ARROW term PERIOD
  {($1, $2, $4)}
| NONTERM ARROW term PERIOD
  {($1, [], $3)};

subterm:
| NONTERM
  {PApp(NT($1), [])}
| NAME 
  {PApp(Name($1), [])}
| LPAR term RPAR
  {$2};

term:
| terms_list
  {match $1 with
   | [x] -> x
   | PApp(h, [])::terms -> PApp(h, terms)
   | _ -> assert false};
| FUN names ARROW term
  {PApp(Fun($2, $4), [])}

terms_list:
| subterm
  {[$1]}
| subterm terms_list
  {$1::$2};

names:
| NAME
  {[$1]}
| NAME names
  {$1::$2};

terminals:
  BEGINT terminals_list END
  {$2};

terminals_list:
| terminal
  {[$1]}
| terminal terminals_list
  {$1::$2};

terminal:
| NAME ARROW INT PERIOD
  {Terminal($1, $3, false)}
| NAME ARROW INT COUNTED PERIOD
  {Terminal($1, $3, true)};