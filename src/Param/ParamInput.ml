(*s Inputs for parametric assumptions.
    See interface for explanation of types. *)

(*i*)
open Poly
open Util
(*i*)

exception InvalidAssumption of string

let fail_assm s = raise (InvalidAssumption s)

(*******************************************************************)
(* \hd{Range expressions, inputs, and challenges} *)

type rvar = string

type rlimitvar = int

type ridxvar = string

type level = LevelFixed of int | LevelOffset of int

let mk_LevelFixed i =
  if i < 1 then fail_assm "Level expression must positive integer" else LevelFixed i

let mk_LevelOffset i =
  if i < 0 then fail_assm "offset in level expression cannot be < 0" else LevelOffset i

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

module EP = MakePoly(struct
  type t = exp_var
  let pp = pp_exp_var
  let equal = (=)
  let compare = compare
end) (IntRing)

type exp_poly = EP.t

type pow_var = (rvar * exp_poly)

type input_monomial = pow_var list

type binder = (ridxvar * (exp_poly * exp_poly))

type qprefix = binder list

type range_expr = {
  re_qprefix        : qprefix;
  re_input_monomial : input_monomial
}

(* \ic{Smart constructor for [range_expr] that ensures ({\bf WF1}).} *)
let mk_range_expr qpref im =

  (* \ic{Disallow $\forall i \in R_1, i \in R_2: \ldots$.}*)
  let bvars = L.map fst qpref in
  if L.length (sorted_nub compare bvars) <> L.length bvars then
    fail_assm "reused range index in input";

  (* \ic{Disallow disallow occurences of $k$ or range indices in $\brack{\alpha,\beta}$.} *)
  let bound_polys = conc_map (fun (_,(a,b)) -> [ a ;b ]) qpref in
  let is_not_Rlimit v = is_Ridx v || v = Level in  
  if L.exists (fun b -> L.exists is_not_Rlimit (EP.vars b)) bound_polys then
    fail_assm "only range limit allowed in upper/lower bound expressions";

  (* \ic{Disallow occurences of unbound range limits.} *)
  let used_ridxs =
    conc_map
      (fun (_,ep) -> conc_map (function Ridx s -> [s] | _ -> []) (EP.vars ep))
      im
  in
  if L.exists (fun v -> not (L.mem v bvars)) used_ridxs then
    fail_assm "unbound range index used in input";

  { re_qprefix = qpref; re_input_monomial = im }

type input = level * range_expr 

type challenge = {
  chal_level : level;
  chal_input_monomial : input_monomial;
}

let mk_challenge l im =
  let vars = conc_map (fun (_,ep) -> EP.vars ep) im in
  if L.exists is_Ridx vars then
    fail_assm "unbound range indices used in challenge."
  else
    { chal_level = l; chal_input_monomial = im }

(*******************************************************************)
(* \hd{Assumption definition} *)

type setting = Symmetric | Asymmetric

type problem_type = Computational | Decisional

type assumption = {
  setting      : setting option;
  problem_type : problem_type option;
  arity        : int option;
  inputs       : input list;       
  challenge    : challenge option;
}

let empty_assm = {
  setting      = None;
  problem_type = None;
  arity        = None;
  inputs       = [];
  challenge    = None;
}

type closed_assumption = {
  ca_setting      : setting;
  ca_problem_type : problem_type;
  ca_arity        : int option;
  ca_inputs       : input list;       
  ca_challenge    : challenge;
}

(*******************************************************************)
(* \hd{Commands in input file} *)

type cmd =
  | Setting       of setting
  | Problem_Type  of problem_type
  | Levels        of int
  | AddInputs     of input list
  | SetChallenge  of challenge

let handle_cmd cmd assm =
  let ensure_none o v s =
     match o with
     | None -> v
     | Some _ -> fail_assm ("cannot set '"^s^"', alreay set for assumption")
  in
  match cmd with
  | Setting s       ->
    ensure_none assm.setting { assm with setting = Some(s) } "setting"
  | Problem_Type pt ->
    ensure_none assm.problem_type { assm with problem_type = Some(pt) } "problem_type"
  | Levels a         ->
    ensure_none assm.arity { assm with  arity = Some(a) } "levels"
  | SetChallenge c  ->
    ensure_none assm.challenge { assm with  challenge = Some(c) } "challenge"
  | AddInputs is    ->
    { assm with inputs = assm.inputs @ is }

let eval_cmds cmds = L.fold_left (fun assm cmd -> handle_cmd cmd assm) empty_assm cmds

(* \ic{Checks for {\bf WF4} and completeness of specification.} *)
let close_assumption a =
  match a.setting, a.problem_type, a.challenge with
  | Some s, Some pt, Some c ->
    let highest =
      (LevelOffset 0)::
      (match a.arity with Some i -> [ LevelFixed i ] | None -> [])
    in
    if pt = Decisional && not ( List.mem c.chal_level highest) then
      fail_assm "challenge must be in target group k for decisional case.";
    { ca_setting = s; 
      ca_problem_type = pt;
      ca_arity = a.arity;
      ca_inputs = a.inputs;
      ca_challenge = c
    }
  | _ -> fail_assm "assumption not fully specified."

(*i*)
(*******************************************************************)
(* \hd{Pretty printing} *)

let pp_level fmt l =
  match l with 
  | LevelFixed i             -> F.fprintf fmt "%i" i
  | LevelOffset i when i = 0 -> F.fprintf fmt "k"
  | LevelOffset i            -> F.fprintf fmt "k - %i" i

let pp_pvar fmt (v,f) =
  if EP.equal f EP.one then
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
    pp_input_monomial chal.chal_input_monomial pp_level chal.chal_level

let pp_assumption fmt assm =
  F.fprintf fmt "assumption: @\n";
  F.fprintf fmt "  %a@\n" (pp_option pp_setting) assm.setting;
  F.fprintf fmt "  arity: %a@\n" (pp_option pp_int) assm.arity;
  F.fprintf fmt "  %a@\n" (pp_option pp_problem_type) assm.problem_type;
  F.fprintf fmt "  @[%a@]\n" pp_inputs assm.inputs;
  F.fprintf fmt "  @[%a@]\n" (pp_option pp_challenge) assm.challenge

let pp_closed_assumption fmt assm =
  F.fprintf fmt "assumption: @\n";
  F.fprintf fmt "  %a@\n" pp_setting assm.ca_setting;
  F.fprintf fmt "  arity: %a@\n" (pp_option pp_int) assm.ca_arity;
  F.fprintf fmt "  %a@\n" pp_problem_type assm.ca_problem_type;
  F.fprintf fmt "  @[%a@]\n" pp_inputs assm.ca_inputs;
  F.fprintf fmt "  @[%a@]\n" pp_challenge assm.ca_challenge

let pp_cmd fmt cmd =
  match cmd with
  | Setting s       -> F.fprintf fmt "setting %a" pp_setting s
  | Problem_Type pt -> F.fprintf fmt "problem_type %a" pp_problem_type pt
  | Levels a        -> F.fprintf fmt "levels %i" a
  | AddInputs is    -> F.fprintf fmt "addInputs %a" pp_inputs is
  | SetChallenge c  -> F.fprintf fmt "setChallenge %a" pp_challenge c
(*i*)
