%{
  (*i*)
  open ParametricInput
  (*i*)
%}

/*s Parser for parametric problems.\\ */

/************************************************************************/
/* \hd{General tokens} */

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
/* \hd{Tokens for Commands} */

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
/* \hd{Tokens for Input} */

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
/* \hd{Priority and associativity} */

/* \ic{Multiplication has the highest precedence.} */
%left PLUS MINUS
%left STAR

/************************************************************************/
/* \hd{Start symbols} */

%start <ParametricInput.cmd list> cmds_t
%%

/************************************************************************/
/* \hd{Inputs and Challenges} */

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
| i = NAT                          { if i = 1 then [] else failwith (string_of_int i^" is not a monomial") }
| p = pow_var                      { [p] }
| p = pow_var; STAR; ps = monomial {  p:: ps }
;  

range_expr :
| FORALL; qps = quants; COLON; pvs = monomial
  { mk_range_expr qps pvs }
| pvs = monomial
  { mk_range_expr [] pvs }
;

offset :
| MINUS; i = NAT { i }

level :
 | i = NAT { mk_LevelFixed i }
 | s = LID; o = offset?
   { if s = "k" then 
       match o with
       | None              -> mk_LevelOffset 0
       | Some i when i > 0 -> mk_LevelOffset i
       | _                 -> failwith "invalid level"
     else
       failwith "invalid level" }
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
| CHALLENGE; m = monomial; AT; l = level; DOT { mk_challenge l m }
;

/************************************************************************/
/* \hd{Commands} */

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
/* \hd{Versions that consume all input} */

cmds_t :
| cs = cmds; EOF { cs }
;