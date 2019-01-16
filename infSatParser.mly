%{
open Syntax
%}

%token <string> NAME
%token <string> NONTERM
%token <int> INT
%token COUNTED
%token ARROW
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
%type <Syntax.preterm> pterm
%type <Syntax.preterm list> pterms
%type <Syntax.preterminals> terminals

%%

main:
  rules terminals EOF
  {($1, $2)};

rules:
  BEGING prules END
  {$2};

prules:
| rule 
  {[$1]}
| rule prules
  {$1::$2};

rule:
| NONTERM names ARROW term PERIOD
  {($1, $2, $4)}
| NONTERM ARROW term PERIOD
  {($1, [], $3)};

pterm:
| NONTERM
  {PApp(NT($1), [])}
| NAME 
  {PApp(Name($1), [])}
| LPAR term RPAR
  {$2};

term:
  pterms
  {match $1 with
   | [x] -> x
   | PApp(h, [])::terms -> PApp(h, terms)
   | _ -> assert false};

pterms:
| pterm
  {[$1]}
| pterm pterms
  {$1::$2};

names:
| NAME
  {[$1]}
| NAME names
  {$1::$2};

terminals:
  BEGINT pterminals END
  {$2};

pterminals:
| terminal
  {[$1]}
| terminal pterminals
  {$1::$2};

terminal:
| NAME ARROW INT PERIOD
  {PTerminal($1, $3, false)}
| NAME ARROW INT COUNTED PERIOD
  {PTerminal($1, $3, true)};