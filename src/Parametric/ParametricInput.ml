(*s Inputs for parametric assumptions.\\ *)
(*i*)
open Poly
open Util
(*i*)

(* For parametric problems, we support all assumptions satisfying
   the following restrictions:
   \begin{enumerate}
   \item The group setting models a symmetric leveled $k$-linear map.
   \item The problem is a computational problem or a decisional
     problem. Decisional problems must be real-or-random and
     the challenge must be in the target group.
   \item The input given to the adversary must be a monomial
   \end{enumerate}
\input{constraint_input} *)


(*******************************************************************)
(* \subsection*{Range expressions} *)

(* \ic{ Random variable $X$, $Y$, \ldots.} *)
type rvar = string

(* \ic{ Range limit variable $l$, $l_1$, $l_2$, \ldots.} *)
type rlimitvar = int

(* \ic{ Range index variable $i$, $j$, \ldots.} *)
type ridxvar = string

(* \ic{%
   A [level] is either [LevelFixed(i)] representing the level $i$
   or [LevelOffset(i)] representing the level $k - i$ where $k$
   is the highest level.} *)
type level = LevelFixed  of int | LevelOffset of int

(* \ic{%
   [exp_var] represents variables that occur in exponents.
   [Rlimit(i)] represents a limit variable~$l_i$,
   [Ridx(s)] represents the index variable $s$,
   and [Level] represents the variable $k$ for the highest level.} *)
type exp_var = Rlimit of rlimitvar | Ridx of ridxvar | Level

(*i*)
let pp_exp_var fmt v =
  match v with
  | Rlimit i when i = -1 -> F.fprintf fmt "l"
  | Rlimit i             -> F.fprintf fmt "l%i" i
  | Ridx v               -> F.fprintf fmt "%s" v
  | Level                -> F.fprintf fmt "k" 
(*i*)

let is_Ridx = function Ridx _ -> true | _ -> false

(* \ic{[EP] is used for polynomials in the exponent.} *)
module EP = MakePoly(struct
  type t = exp_var
  let pp = pp_exp_var
end) (IntRing)

type exp_poly = EP.t

(* \ic{[("X",f)] represents $X^{f}$.} *)
type pow_var = (rvar * exp_poly)

(* \ic{The list represent the product of the [pow_var]s} *)
type input_monomial = pow_var list

(* \ic{Range index binder $r \in [\alpha, \beta]$ represented by $(r,(\alpha,\beta))$.} *)
type binder = (ridxvar * (exp_poly * exp_poly))

(* \ic{A quantifier prefix consists of a list of range index binders.} *)
type qprefix = binder list

(* \ic{%
   A range expression consist of the quantifier prefix and the monomial. 
   As an example, consider $\forall i \in [0,l]: X^i * Y^l$.} *)
type range_expr =
  { re_qprefix        : qprefix;
    re_input_monomial : input_monomial
  }

(* \ic{An input consists of a level and a range expression.} *)
type input = level * range_expr 

(* \ic{A challenge consists of a level and an input monomial.} *)
type challenge = level * input_monomial

(*******************************************************************)
(* \subsection*{Assumption definition} *)

type setting = Symmetric | Asymmetric

type problem_type = Computational | Decisional

(* \ic{%
    An assumption must fix the setting, the problem type, and \emph{can}
    either fix the arity $k$ to a specific value $i$ or consider $k$ as
    a variable.
    We use [option] types to support partially and fully specified assumptions
    with the same type.} *)
type assumption =
  { setting      : setting option;
    problem_type : problem_type option;
    arity        : int option;
    inputs       : input list;       
    challenge    : challenge option;
  }

let empty_assm =
  { setting      = None;
    problem_type = None;
    arity        = None;
    inputs       = [];
    challenge    = None;
  }

(*******************************************************************)
(* \subsection*{Commands in input file} *)

(* \ic{%
   The user defines an assumption by giving a sequence of
   commands that set/extend a partially specified assumption.
   Extension is used with [AddInputs] which allows the user to
   define the adversary input in multiple steps.} *)
type cmd =
  | Setting       of setting
  | Problem_Type  of problem_type
  | Arity         of int
  | AddInputs     of input list
  | SetChallenge  of challenge

let handle_cmd cmd assm =
  let ensure_none o v s =
     match o with
     | None -> v
     | Some _ -> failwith ("cannot set '"^s^"', alreay set for assumption")
  in
  match cmd with
  | Setting s       ->
    ensure_none assm.setting { assm with setting = Some(s) } "setting"
  | Problem_Type pt ->
    ensure_none assm.problem_type { assm with problem_type = Some(pt) } "problem_type"
  | Arity a         ->
    ensure_none assm.arity { assm with  arity = Some(a) } "arity"
  | SetChallenge c  ->
    ensure_none assm.challenge { assm with  challenge = Some(c) } "challenge"
  | AddInputs is    ->
    { assm with inputs = assm.inputs @ is }

let eval_cmds cmds = L.fold_left (fun assm cmd -> handle_cmd cmd assm) empty_assm cmds

(*i*)
(* \begin{pretty} *)
(*******************************************************************)
(* \subsection*{Pretty printing} *)

let pp_level fmt l =
  match l with 
  | LevelFixed i  -> F.fprintf fmt "%i" i
  | LevelOffset i -> F.fprintf fmt "k - %i" i

let pp_pvar fmt (v,f) =
  if f = EP.one then
    F.fprintf fmt "%s" v
  else if EP.is_var f || EP.is_const f then
    F.fprintf fmt "%s^%a" v EP.pp f  
  else 
    F.fprintf fmt "%s^(%a)" v EP.pp f

let pp_input_monomial fmt f =
  match f with
  | [] -> 
    F.fprintf fmt "1"
  | _  ->
    F.fprintf fmt "%a" (pp_list "*" pp_pvar) f

let pp_qprefix fmt (a,b) =
  F.fprintf fmt "[%a,%a]"
    EP.pp a EP.pp b

let pp_range fmt (s,qp) =
  F.fprintf fmt "%s in %a" s pp_qprefix qp

let pp_rexpr fmt re =
  match re.re_qprefix with
  | [] -> pp_input_monomial fmt re.re_input_monomial
  | qps ->
    F.fprintf fmt "All %a. %a"
      (pp_list "," pp_range) qps
      pp_input_monomial re.re_input_monomial

let pp_rexpr_level fmt (l,re) =
  F.fprintf fmt "%a @@ level %a" pp_rexpr re pp_level l

let pp_setting fmt s =
  F.fprintf fmt "%ssymmetric"
    (match s with
     | Symmetric -> ""
     | Asymmetric -> "a")

let pp_problem_type fmt pt =
  F.fprintf fmt "%s"
    (match pt with
     | Decisional    -> "decisional"
     | Computational -> "computational")

let pp_inputs fmt inp =
  F.fprintf fmt "inputs: @\n  %a@\n@\n"
    (pp_list "@\n  " (fun fmt (i,re) -> F.fprintf fmt "%i: %a" i pp_rexpr_level re))
    (mapi' (fun i inp -> (i,inp)) inp)

let pp_challenge fmt chal =
  F.fprintf fmt "challenge: %a @@ level %a\n\n"
    pp_input_monomial (snd chal) pp_level (fst chal)

let pp_assumption fmt assm =
  F.fprintf fmt "assumption: @\n";
  F.fprintf fmt "  %a@\n" (pp_option pp_setting) assm.setting;
  F.fprintf fmt "  arity: %a@\n" (pp_option pp_int) assm.arity;
  F.fprintf fmt "  %a@\n" (pp_option pp_problem_type) assm.problem_type;
  F.fprintf fmt "  @[%a@]\n" pp_inputs assm.inputs;
  F.fprintf fmt "  @[%a@]\n" (pp_option pp_challenge) assm.challenge

let pp_cmd fmt cmd =
  match cmd with
  | Setting s       -> F.fprintf fmt "setting %a" pp_setting s
  | Problem_Type pt -> F.fprintf fmt "problem_type %a" pp_problem_type pt
  | Arity a         -> F.fprintf fmt "arity %i" a
  | AddInputs is    -> F.fprintf fmt "addInputs %a" pp_inputs is
  | SetChallenge c  -> F.fprintf fmt "setChallenge %a" pp_challenge c
(*i*)
