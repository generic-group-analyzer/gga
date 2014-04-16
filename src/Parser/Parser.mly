%{
  (** Parser for parametric case. *)
  open Parametric_Input

%}

%token EOF

/************************************************************************/
/* Tokens for ??? */

%token FORALL
%token INPUT
%token CHALLENGE
%token IN
%token LBRACKET
%token RBRACKET
%token LPAREN
%token RPAREN

%token DOT
%token COLON
%token COMMA
%token AT

/************************************************************************/
/* Tokens for ??? */
%token <string> UID (* uppercase identifier *)
%token <string> LID (* lowercase identifier *)
%token <int> RLIMIT (* range limit *)


%token STAR
%token PLUS
%token MINUS

%token CARET

%token <int> NAT

/************************************************************************/
/* Priority and associativity */

%left PLUS
%left MINUS

%start <Parametric_Input.rexpr> rexpr_t

%start  <Parametric_Input.input list> inputs_t

%start <Parametric_Input.challenge> challenge_t


%%

poly :
| i = NAT
  { EP.const i }
| i = RLIMIT
  { EP.var (Rlimit i) }
| s = LID
  { EP.var (Ridx s) }
| LPAREN; f = poly; RPAREN
  { f }
| f = poly; PLUS; g = poly
  { EP.add f g }
| f = poly; STAR; g = poly
  { EP.mult f g }
| f = poly; MINUS; g = poly
  { EP.minus f g }
| MINUS; f = poly
  { EP.opp f }
;

exponent :
| { EP.one }
| CARET; f = poly
  { f }
;

pow_var : 
| s = UID; f = exponent
  { (s,f) }
;

ubound :
| l = RLIMIT
  { (l,0) }
| l = RLIMIT; PLUS; n = NAT
  { (l,n) }
| l = RLIMIT; MINUS; n = NAT
  { (l,-n) }
;

quant :
| r = LID; IN; LBRACKET; i = NAT; COMMA; ub = ubound; RBRACKET
  { (r,(i,fst ub, snd ub)) }
;

quants :
| q = quant
  { [q] }
| q = quant; COMMA; qs = quants
  { q::qs }
;

monomial :
| i = NAT
  { if i = 1 then [] else failwith "FIXME" }
| p = pow_var
  { [p] }
| p = pow_var; STAR; ps = monomial
  { p:: ps }
;  

rexpr :
| FORALL; qps = quants; COLON; pvs = monomial
  { {re_qprefix = qps; re_input_monomial = pvs } }
| pvs = monomial
  { {re_qprefix = []; re_input_monomial = pvs } }
;

level :
 | i = NAT { LevelFixed i }
 | s = LID { if s = "k" then LevelOffset 0 else failwith "FIXME" }
 (* FIXME: add support for offset *)
;

rexprs :
| i = rexpr
  { [i] }
| i = rexpr; COMMA; is = rexprs
  { i::is }
;

inputs :
| INPUT; LBRACKET; ims = rexprs; RBRACKET; AT; l = level; DOT
  { List.map (fun im -> (l,im)) ims }
;

challenge :
| CHALLENGE; m = monomial; AT; l = level; DOT
  { (l, m) }

/************************************************************************/
/* Versions that consume all input */

inputs_t :
| i = inputs; EOF
  { i }
;

rexpr_t :
| re = rexpr; EOF
  { re }
;

challenge_t :
| c = challenge; EOF
  { c }
