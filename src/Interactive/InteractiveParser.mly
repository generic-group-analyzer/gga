%{
  (*i*)
  open InteractiveInput
  open InteractiveEval
  (*i*)
%}

/*s Parser for interactive assumptions */

/************************************************************************/
/* \hd{General tokens} */

%token EOF
%token DOT
%token COMMA
%token IN
%token COLON
%token LAND

%token LBRACK
%token RBRACK
%token LPAR
%token RPAR

%token EQ
%token INEQ
%token SAMP
%token SEMICOLON

/************************************************************************/
/* \hd{Tokens for Commands} */

%token INP
%token ORACLE
%token WIN
%token RETURN

/************************************************************************/
/* \hd{Tokens for Input} */

%token <string> VAR   /* uppercase identifier */

%token <string> GROUP
%token FIELD

%token EXP
%token STAR
%token PLUS
%token MINUS

%token <int> NAT

/************************************************************************/
/* \hd{Priority and associativity} */

/* \ic{Multiplication has the highest precedence.} */
%left PLUS MINUS
%left STAR

/************************************************************************/
/* \hd{Start symbols} */

%type <InteractiveEval.cmd list> cmds_t

%start cmds_t
%%

/************************************************************************/
/* \hd{Commands} */

poly :
| i = NAT                   { RP.from_int i }
| v = VAR                   { RP.var v }
| f = poly; PLUS; g = poly  { RP.add f g }
| f = poly; STAR; g = poly  { RP.mult f g }
| f = poly; MINUS; g = poly { RP.minus f g }
| MINUS; f = poly           { RP.opp f }
| LPAR;  f = poly; RPAR     { f }
| f = poly; EXP; i = NAT    { RP.ring_exp f i }
;

param_type :
| s = GROUP { Group s }
| FIELD { Field }
;

samp_var : v = VAR; SAMP; GROUP; SEMICOLON
  { v }
;

typed_var :
| v = VAR; COLON; ty = param_type;
  { { tid_id = v; tid_ty = ty } } 
;
cond :
| p1 = poly; EQ; p2 = poly;
  { (RP.minus p1 p2, Eq) }
| p1 = poly; INEQ; p2 = poly;
  { (RP.minus p1 p2, InEq) }
;

poly_group:
| p = poly; IN; g = GROUP
  { (p,g) }
; /* fix this */

cmd :
| INP; LBRACK; ps = separated_nonempty_list(COMMA,poly); RBRACK; IN; GROUP; DOT
  { AddInput(ps) }
| ORACLE; oname = VAR; LPAR; params = separated_list(COMMA,typed_var); RPAR;
  EQ; orvar = list(samp_var);
  RETURN; LPAR; ps = separated_list(COMMA,poly_group); RPAR;
  DOT
  { AddOracle(oname,params,orvar,ps) }
| WIN; LPAR; params = separated_list(COMMA,typed_var); RPAR;
  EQ;  LPAR; conds  = separated_list(LAND,cond); RPAR;
  DOT
  { SetWinning(params,conds) }
;

/************************************************************************/
/* \hd{Versions that consume all input} */

cmds_t : cs = list(cmd); EOF { cs };