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
%token TO

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
%token EMAPS
%token ISOS

/************************************************************************/
/* \hd{Tokens for Input} */

%token <string> VAR   /* uppercase identifier */

%token <string> GROUP
%token FIELD

%token EXP
%token STAR
%token PLUS
%token MINUS

%token <int> INT

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
| i = INT                   { RP.from_int i }
| v = VAR                   { RP.var v }
| f = poly; PLUS; g = poly  { RP.add f g }
| f = poly; STAR; g = poly  { RP.mult f g }
| f = poly; MINUS; g = poly { RP.minus f g }
| MINUS; f = poly           { RP.opp f }
| LPAR;  f = poly; RPAR     { f }
| v = VAR; EXP; i = INT
{ RP.var_exp v i }
| f = poly; EXP; i = INT
{ if i < 0
  then failwith "negative exponent only allowed for variables"
  else RP.ring_exp f i }
;

param_type :
| s = GROUP { Group s }
| FIELD { Field }
;

samp_vars : SAMP; vs = separated_nonempty_list(COMMA,VAR); SEMICOLON
  { vs }
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


polys_group:
| LBRACK; ps = separated_list(COMMA,poly); RBRACK; IN; g = GROUP
{ List.map (fun p -> (p,g)) ps}

iso :
| dom = GROUP; TO; codom = GROUP { { iso_dom = dom; iso_codom = codom } }
;

emap :
| dom = separated_nonempty_list(STAR,GROUP); TO; codom = GROUP
  { { em_dom = dom; em_codom = codom } }
;

cmd :
| EMAPS; emaps = separated_nonempty_list(COMMA,emap); DOT
  { AddMaps emaps }
| ISOS; isos = separated_nonempty_list(COMMA,iso); DOT
  { AddIsos isos }

| INP; LBRACK; ps = separated_nonempty_list(COMMA,poly); RBRACK; IN; g = GROUP; DOT
  { AddInput(ps,g) }
| ORACLE; oname = VAR; LPAR; params = separated_list(COMMA,typed_var); RPAR;
  EQ; orvar = list(samp_vars);
  RETURN; ps = separated_list(COMMA,polys_group); DOT
  { AddOracle(oname,params,List.concat orvar,List.concat ps) }
| WIN; LPAR; params = separated_list(COMMA,typed_var); RPAR;
  EQ;  LPAR; conds  = separated_list(LAND,cond); RPAR;
  DOT
  { SetWinning(params,conds) }
;

/************************************************************************/
/* \hd{Versions that consume all input} */

cmds_t : cs = list(cmd); EOF { cs };