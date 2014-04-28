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

%token LBRACKET
%token RBRACKET
%token LPAREN
%token RPAREN

/************************************************************************/
/* \hd{Tokens for Commands} */

%token EMAPS
%token ISOS
%token INPUT_LEFT
%token INPUT_RIGHT
%token INPUT
%token CHALLENGE

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
| LPAREN; f = poly; RPAREN  { f }
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
| INPUT_LEFT; LBRACKET; ps = separated_nonempty_list(COMMA,poly); RBRACKET; IN; gid = GID; DOT
  { AddInputLeft(L.map (fun p -> { ge_rpoly = p; ge_group = gid }) ps) }
| INPUT_RIGHT; LBRACKET; ps = separated_nonempty_list(COMMA,poly); RBRACKET; IN; gid = GID; DOT
  { AddInputRight(L.map (fun p -> { ge_rpoly = p; ge_group = gid }) ps) }
| INPUT; LBRACKET; ps = separated_nonempty_list(COMMA,poly); RBRACKET; IN; gid = GID; DOT
  { AddInput(L.map (fun p -> { ge_rpoly = p; ge_group = gid }) ps) }
| CHALLENGE; p = poly; IN; gid = GID; DOT
  { SetChallenge({ ge_rpoly = p; ge_group = gid }) }

;

/************************************************************************/
/* \hd{Versions that consume all input} */

cmds_t : cs = list(cmd); EOF { cs };