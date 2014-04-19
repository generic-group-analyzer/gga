%{
  (*i*)
  open ParametricInput
  (*i*)
%}

/*s Parser for parametric problems.\\ */

/************************************************************************/
/* \ic{ General tokens} */

%token EOF
%token DOT
%token COLON
%token COMMA
%token AT

%token LBRACKET
%token RBRACKET
%token LPAREN
%token RPAREN

/************************************************************************/
/* \ic{Tokens for Commands} */

%token INPUT
%token CHALLENGE
%token SETTING
%token SYMMETRIC
%token ASYMMETRIC
%token PROBLEM_TYPE
%token COMPUTATIONAL
%token DECISIONAL
%token ARITY

/************************************************************************/
/* \ic{Tokens for Input} */

%token IN
%token FORALL

%token <string> UID /* uppercase identifier */
%token <string> LID /* lowercase identifier */
%token <int> RLIMIT /* range limit */


%token STAR
%token PLUS
%token MINUS
%token CARET

%token <int> NAT

/************************************************************************/
/* \ic{Priority and associativity} */

%left STAR
%left PLUS
%left MINUS

/************************************************************************/
/* \ic{Start symbols} */

%start <ParametricInput.range_expr> range_expr_t

%start  <ParametricInput.input list> inputs_t

%start <ParametricInput.challenge> challenge_t

%start <ParametricInput.cmd list> cmds_t
%%

/************************************************************************/
/* \ic{Inputs and Challenges} */

poly :
| i = NAT                   { EP.const i }
| i = RLIMIT                { EP.var (Rlimit i) }
| s = LID                   { EP.var (Ridx s) }
| LPAREN; f = poly; RPAREN  { f }
| f = poly; PLUS; g = poly  { EP.add f g }
| f = poly; STAR; g = poly  { EP.mult f g }
| f = poly; MINUS; g = poly { EP.minus f g }
| MINUS; f = poly           { EP.opp f }
;

exponent :
|                 { EP.one }
| CARET; f = poly { f }
;

pow_var : 
| s = UID; f = exponent { (s,f) }
;

quant :
| r = LID; IN; LBRACKET; a = poly; COMMA; b = poly; RBRACKET
  { (r,(a,b)) }
;

quants :
| q = quant                     { [q] }
| q = quant; COMMA; qs = quants { q::qs }
;

monomial :
| i = NAT                          { if i = 1 then [] else failwith "FIXME" }
| p = pow_var                      { [p] }
| p = pow_var; STAR; ps = monomial { p:: ps }
;  

range_expr :
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

range_exprs :
| i = range_expr                          { [i] }
| i = range_expr; COMMA; is = range_exprs { i::is }
;

input_list:
| LBRACKET; ims = range_exprs; RBRACKET; AT; l = level
  { List.map (fun im -> (l,im)) ims }
;

input_lists:
| il = input_list                           { [il] }
| il = input_list; COMMA; ils = input_lists { il::ils }
;

inputs :
| INPUT; ims = input_lists; DOT { List.concat ims }
; 

challenge :
| CHALLENGE; m = monomial; AT; l = level; DOT { (l, m) }
;

/************************************************************************/
/* \ic{Commands} */

setting :
| SYMMETRIC  { Symmetric } 
| ASYMMETRIC { Asymmetric }
;

problem_type :
| COMPUTATIONAL { Computational }
| DECISIONAL    { Decisional }
;

cmd :
| SETTING; s = setting; DOT            { Setting s }
| PROBLEM_TYPE; pt = problem_type; DOT { Problem_Type pt }
| ARITY; i = NAT; DOT                  { Arity i }
| is = inputs                          { AddInputs is }
| c = challenge                        { SetChallenge c }
;

cmds :
|                    { [] }
| c = cmd; cs = cmds { c::cs }
;

/************************************************************************/
/* \ic{Versions that consume all input} */

inputs_t :
| i = inputs; EOF { i }
;

range_expr_t :
| re = range_expr; EOF { re }
;

challenge_t :
| c = challenge; EOF { c }
;

cmds_t :
| cs = cmds; EOF { cs }
;