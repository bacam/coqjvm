%{
  open Ill_absyn
%}

%token<string> ID AXIOM
%token LET TENSOR BE IN LAMBDA COLON DOT BANG AND
%token LOLLI TOP STAR LPAREN RPAREN EOF END P1 P2 OK FAIL

%type<Ill_absyn.formula_absyn> full_formula

%type<Ill_absyn.formula_absyn * Ill_absyn.formula_absyn> formula_pair

%type<Ill_absyn.formula_absyn * Ill_absyn.formula_absyn * Ill_absyn.formula_absyn> specification

%type<Ill_absyn.term_absyn> full_term

%type<(Ill_absyn.formula_absyn * Ill_absyn.formula_absyn * Ill_absyn.term_absyn * bool) list> input

%start full_formula
%start formula_pair
%start specification
%start full_term
%start input

%nonassoc ID STAR
%nonassoc LET LAMBDA
%nonassoc LAM
%left APP
%left AND
%left TENSOR
%right LOLLI
%right BANG P1 P2 AXIOM
%nonassoc LPAREN

%%

input: inputblocks EOF { $1 }

inputblocks:
/* empty */      { [] }
| inputblock inputblocks {$1::$2 }

inputblock: formula formula term expected { ($1, $2, $3, $4) }

expected:
  OK { true }
| FAIL { false }

full_formula: formula EOF { $1 }

formula_pair: formula formula EOF { ($1, $2) }

specification: formula formula formula { ($1,$2,$3) }

full_term: term EOF { $1 }

formula:
  TOP                    { F_top }
| ID                     { F_atom $1 }
| formula TENSOR formula { F_tensor ($1, $3) }
| formula AND formula    { F_and ($1, $3) }
| formula LOLLI formula  { F_lolli ($1, $3) }
| BANG formula           { F_bang $2 }
| LPAREN formula RPAREN  { $2 }

term:
  ID                     { T_var $1 }
| STAR                   { T_star }
| term TENSOR term       { T_tensor_intro ($1, $3) }
| LET ID TENSOR ID BE term IN term END { T_tensor_elim ($2, $4, $6, $8) }
| term AND term          { T_and_intro ($1, $3) }
| P1 term                { T_and_elim1 $2 }
| P2 term                { T_and_elim2 $2 }
| LAMBDA ID COLON formula DOT term %prec LAM { T_lolli_intro ($2, $4, $6) }
| term term %prec APP    { T_lolli_elim ($1, $2) }
| BANG term              { T_bang_intro $2 }
| LET BANG ID BE term IN term END { T_bang_elim ($3, $5, $7) }
| LPAREN term RPAREN     { $2 }
| AXIOM term             { T_axiom ($1,$2) }
| LET ID BE term IN term END { T_let ($2,$4,$6) }
