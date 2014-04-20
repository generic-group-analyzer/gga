(*s Inputs for parametric assumptions. *)

exception InvalidAssumption of string

(*******************************************************************)
(* \hd{Range expressions, inputs, and challenges} *)

(* \ic{ Random variable $X$, $Y$, \ldots.} *)
type rvar = string

(* \ic{ Range limit variable $l$, $l_1$, $l_2$, \ldots.} *)
type rlimitvar = int

(* \ic{ Range index variable $i$, $j$, \ldots.} *)
type ridxvar = string

(* \ic{%
   A [level] is either [LevelFixed(i)] representing the level $i$
   or [LevelOffset(i)] representing the level $k - i$ where $k$
   is the highest level. } *)
type level = private LevelFixed of int | LevelOffset of int

(* \ic{Smart constructor that fails for integer $<1$ to ensure ({\bf WF3}).} *)
val mk_LevelFixed : int -> level

(* \ic{[mk_LevelOffset i] fails if [i < 0] to ensure ({\bf WF3}).} *)
val mk_LevelOffset : int -> level

(* \ic{%
   [exp_var] represents variables that occur in exponents.
   [Rlimit(i)] represents a limit variable~$l_i$,
   [Ridx(s)] represents the index variable $s$,
   and [Level] represents the variable $k$ for the highest level.} *)
type exp_var = Rlimit of rlimitvar | Ridx of ridxvar | Level

(* \ic{[EP] is used for polynomials in the exponent.} *)
module EP : PolyInterfaces.Poly with type var = exp_var and type coeff = Big_int.big_int

type exp_poly = EP.t

(* \ic{[("X",f)] represents $X^{f}$.} *)
type pow_var = rvar * exp_poly

(* \ic{The list represent the product of the [pow_var]s} *)
type input_monomial = pow_var list

(* \ic{Range index binder $r \in [\alpha, \beta]$ represented by $(r,(\alpha,\beta))$.} *)
type binder = ridxvar * (exp_poly * exp_poly)

(* \ic{A quantifier prefix consists of a list of range index binders.} *)
type qprefix = binder list

(* \ic{%
   A range expression consist of the quantifier prefix and the monomial. 
   As an example, consider $\forall i \in [0,l]: X^i * Y^l$.} *)
type range_expr =  private{
  re_qprefix : qprefix;
  re_input_monomial : input_monomial;
}

(* \ic{Smart constructor for [range_expr] that ensures ({\bf WF1}).} *)
val mk_range_expr : qprefix -> input_monomial -> range_expr

(* \ic{An input consists of a level and a range expression.} *)
type input = level * range_expr

(* \ic{A challenge consists of a level and an input monomial.} *)
type challenge = private {
  chal_level : level;
  chal_input_monomial : input_monomial;
}

(* \ic{Smart constructor for challenge that ensures ({\bf WF2}).} *)
val mk_challenge : level -> input_monomial -> challenge

(*******************************************************************)
(* \hd{Assumption definition} *)

type setting = Symmetric | Asymmetric

type problem_type = Computational | Decisional

(* \ic{%
    An assumption must fix the setting, the problem type, and \emph{can}
    either fix the arity $k$ to a specific value $i$ or consider $k$ as
    a variable.
    We use [option] types to support partially specified assumptions.} *)
type assumption = {
  setting : setting option;
  problem_type : problem_type option;
  arity : int option;
  inputs : input list;
  challenge : challenge option;
}

(* \ic{A closed assumption is fully specified and guaranteed to be well-formed.} *)
type closed_assumption = private {
  ca_setting : setting;
  ca_problem_type : problem_type;
  ca_arity : int option;
  ca_inputs : input list;
  ca_challenge : challenge;
}

(*******************************************************************)
(* \hd{Commands in input file} *)

(* \ic{%
   The user defines an assumption by giving a sequence of
   commands that set/extend a partially specified assumption.
   Extension is used with [AddInputs] which allows the user to
   define the adversary input in multiple steps.} *)
type cmd =
  | Setting of setting
  | Problem_Type of problem_type
  | Arity of int
  | AddInputs of input list
  | SetChallenge of challenge

val is_Ridx : exp_var -> bool

(* \ic{[eval_cmds cmds] executes the commands [cmds] and returns the resulting assumption.}*)
val eval_cmds : cmd list -> assumption

(* \ic{Closes the given assumption. Fails if incomplete or not well-formed.} *)
val close_assumption : assumption -> closed_assumption

(*i*)
(*********************************************************************)
(* \hd{Pretty printing} *)

val pp_exp_var :           Util.F.formatter -> exp_var                   -> unit
val pp_level :             Util.F.formatter -> level                     -> unit
val pp_pvar :              Util.F.formatter -> string * EP.t             -> unit
val pp_input_monomial :    Util.F.formatter -> (string * EP.t) list      -> unit
val pp_qprefix :           Util.F.formatter -> EP.t * EP.t               -> unit
val pp_range :             Util.F.formatter -> string * (EP.t * EP.t)    -> unit
val pp_rexpr :             Util.F.formatter -> range_expr                -> unit
val pp_rexpr_level :       Util.F.formatter -> level * range_expr        -> unit
val pp_setting :           Util.F.formatter -> setting                   -> unit
val pp_problem_type :      Util.F.formatter -> problem_type              -> unit
val pp_inputs :            Util.F.formatter -> (level * range_expr) list -> unit
val pp_challenge :         Util.F.formatter -> challenge                 -> unit
val pp_assumption :        Util.F.formatter -> assumption                -> unit
val pp_closed_assumption : Util.F.formatter -> closed_assumption         -> unit
val pp_cmd :               Util.F.formatter -> cmd                       -> unit

(*i*)