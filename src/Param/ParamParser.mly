%{
  (*i*)
  open Util
  open ParamInput
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
%token LEVELS

/************************************************************************/
/* \hd{Tokens for Input} */

%token IN
%token FORALL

%token <string> VARU /* uppercase identifier */
%token <string> VARL /* lowercase identifier */
%token <int> RLIMIT  /* range limit */
%token VARLEVEL      /* the highest level l */

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

%type  <ParamInput.cmd list> cmds_t

%start cmds_t
%%

/************************************************************************/
/* \hd{Inputs and Challenges} */

poly :
| i = NAT                   { EP.from_int i }
| i = RLIMIT                { EP.var (Rlimit i) }
| s = VARL                  { EP.var (Ridx s) }
| VARLEVEL                  { EP.var (Level) }
| f = poly; PLUS; g = poly  { EP.add f g }
| f = poly; STAR; g = poly  { EP.mult f g }
| f = poly; MINUS; g = poly { EP.minus f g }
| MINUS; f = poly           { EP.opp f }
| LPAREN; f = poly; RPAREN  { f }
;

/* \ic{%
   Polynomial expression that can be used in exponent without parentheses.
   Required because otherwise there is a conflict between $*$ in exponent
   and in monomial.} */
poly_no_paren :
| i = NAT                    { EP.from_int i }
| i = RLIMIT                 { EP.var (Rlimit i) }
| s = VARL                   { EP.var (Ridx s) }
| VARLEVEL                   { EP.var (Level) }
;

exponent :
 | CARET; f = poly_no_paren              { f }
 | CARET; LPAREN; f = poly; RPAREN { f }
;

pow_var : s = VARU; f = exponent? { (s,from_opt id EP.one f) };

quant : r = VARL; IN; LBRACKET; a = poly; COMMA; b = poly; RBRACKET { (r,(a,b)) };

quants : qs = separated_nonempty_list(COMMA, quant) {qs};

monomial :
| ps = separated_nonempty_list(STAR,pow_var)
  {  ps }
| i = NAT                          
  { if i = 1 then [] else failwith (F.sprintf "%i is not a monomial" i) }
;  

range_expr :
| FORALL; qps = quants; COLON; pvs = monomial { mk_range_expr qps pvs }
| pvs = monomial                              { mk_range_expr [] pvs }
;

offset : MINUS; i = NAT { i };

level :
 | i = NAT { mk_LevelFixed i }
 | VARLEVEL; o = offset?
   { match o with
     | None              -> mk_LevelOffset 0
     | Some i when i > 0 -> mk_LevelOffset i
     | _                 -> failwith "invalid level"
   }
;

input_list:
| LBRACKET; ims = separated_nonempty_list(COMMA,range_expr); RBRACKET; AT; l = level
  { List.map (fun im -> (l,im)) ims }
;

inputs : ims = separated_nonempty_list(COMMA,input_list); DOT { List.concat ims };

challenge : m = monomial; AT; l = level; DOT { mk_challenge l m };

/************************************************************************/
/* \hd{Commands} */

setting :
| SYMMETRIC  { Symmetric } 
| ASYMMETRIC { fail_assm "Asymmetric assumptions not supported in parametric case." }
;

problem_type :
| COMPUTATIONAL { Computational }
| DECISIONAL    { Decisional }
;

cmd :
| SETTING; s = setting; DOT            { Setting s }
| PROBLEM_TYPE; pt = problem_type; DOT { Problem_Type pt }
| LEVELS; i = NAT; DOT                 { Levels i }
| INPUT; is = inputs                   { AddInputs is }
| CHALLENGE; c = challenge             { SetChallenge c }
;

/************************************************************************/
/* \hd{Versions that consume all input} */

cmds_t : cs = list(cmd); EOF { cs };
