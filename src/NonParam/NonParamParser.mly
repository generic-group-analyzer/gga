%{
  (*i*)
  open Util
  open NonParamInput
  (*i*)
%}

/*s Parser for non-parametric assumptions */

/************************************************************************/
/* \hd{General tokens} */

%token EOF
%token DOT
%token COMMA
%token IN
%token TO

%token LBRACK
%token RBRACK
%token LPAR
%token RPAR

/************************************************************************/
/* \hd{Tokens for Commands} */

%token EMAPS
%token ISOS
%token INP_L
%token INP_R
%token INP
%token CHAL
%token COMP

/************************************************************************/
/* \hd{Tokens for Input} */


%token <string> VARU /* uppercase identifier */
%token <string> GID  /* group identifier */

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

%type  <NonParamInput.cmd list> cmds_t

%start cmds_t
%%

/************************************************************************/
/* \hd{Commands} */

poly :
| i = NAT                   { RP.from_int i }
| v = VARU                  { RP.var v }
| f = poly; PLUS; g = poly  { RP.add f g }
| f = poly; STAR; g = poly  { RP.mult f g }
| f = poly; MINUS; g = poly { RP.minus f g }
| MINUS; f = poly           { RP.opp f }
| LPAR; f = poly; RPAR      { f }
;

poly_comp :
| LPAR; p = poly; COMMA; ps = separated_nonempty_list(COMMA,poly); RPAR;
  { p::ps }
| p = poly
  { [p] }
;
iso :
| dom = GID; TO; codom = GID { { iso_dom = dom; iso_codom = codom } }
;

emap :
| dom = separated_nonempty_list(STAR,GID); TO; codom = GID
  { { em_dom = dom; em_codom = codom } }
;

cmd :
| EMAPS; emaps = separated_nonempty_list(COMMA,emap); DOT
  { AddMaps emaps }
| ISOS; isos = separated_nonempty_list(COMMA,iso); DOT
  { AddIsos isos }
| COMP; i = NAT; DOT
  { SetPrimeNum i }
| INP_L; LBRACK; pss = separated_nonempty_list(COMMA,poly_comp); RBRACK; IN; gid = GID; DOT
  { AddInputLeft(L.map (fun ps -> { ge_rpoly = ps; ge_group = gid }) pss) }
| INP_R; LBRACK; pss = separated_nonempty_list(COMMA,poly_comp); RBRACK; IN; gid = GID; DOT
  { AddInputRight(L.map (fun ps -> { ge_rpoly = ps; ge_group = gid }) pss) }
| INP; LBRACK; pss = separated_nonempty_list(COMMA,poly_comp); RBRACK; IN; gid = GID; DOT
  { AddInput(L.map (fun ps -> { ge_rpoly = ps; ge_group = gid }) pss) }
| CHAL; ps = poly_comp; IN; gid = GID; DOT
  { SetChallenge({ ge_rpoly = ps; ge_group = gid }) }

;

/************************************************************************/
/* \hd{Versions that consume all input} */

cmds_t : cs = list(cmd); EOF { cs };