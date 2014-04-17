open Poly
open Util

module F = Format


(*******************************************************************)
(* Range expressions *)

(* random variable (assume: polynomials in L are monomials) *)
type rvar = string

type rlimit_var = int

type ridx_var = string

type level =
  | LevelFixed  of int (* Fixed(i) represents the level i *)
  | LevelOffset of int (* Offset(i) represents the level k - i *)

let pp_level fmt l =
  match l with 
  | LevelFixed i  -> F.fprintf fmt "%i" i
  | LevelOffset i -> F.fprintf fmt "k - %i" i

type exp_var = 
  | Rlimit of rlimit_var  (* l_i *)
  | Ridx   of ridx_var    (* lower-case string *)
  | Level                 (* k   *)

let is_Ridx = function Ridx _ -> true | _ -> false

let pp_exp_var fmt v =
  match v with
  | Rlimit i when i = -1 -> F.fprintf fmt "l"
  | Rlimit i             -> F.fprintf fmt "l%i" i
  | Ridx v               -> F.fprintf fmt "%s" v
  | Level                -> F.fprintf fmt "k" 

module ExpPoly = MakePoly(struct
  type t = exp_var
  let pp = pp_exp_var
end) (IntRing)

module EP = ExpPoly

type exp_poly = EP.t

type pvar = (rvar * exp_poly)

(* assoc lists (FIXME: switch to maps) *)
type input_monomial = pvar list

(* quantifier prefix [ci, li + di] *)
type qprefix = (ridx_var * (int * rlimit_var * int)) list

type rexpr =
  { re_qprefix        : qprefix;
    re_input_monomial : input_monomial
  }

type input = level * rexpr 

type challenge = level * input_monomial

let mk_rexpr pref mon =
  { re_qprefix = pref; re_input_monomial = mon }


(*******************************************************************)
(* Pretty printing *)


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

let pp_qprefix fmt (c,l,d) =
  F.fprintf fmt "[%i,%a%s]"
    c pp_exp_var (Rlimit l) (if d <> 0 then " + "^(string_of_int d) else "")

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

(*******************************************************************)
(* Assumption definition *)

type setting = Symmetric | Asymmetric

type problem_type = Decisional | Computational

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

let pp_setting fmt s =
  F.fprintf fmt "%ssymmetric"
    (match s with
     | Symmetric -> ""
     | Asymmetric -> "a")

let pp_problem_type fmt pt =
  F.fprintf fmt "%s"
    (match pt with
     | Decisional -> "decisional"
     | Computational -> "computational")

let pp_inputs fmt inp =
  F.fprintf fmt "inputs: @\n  %a@\n@\n"
    (pp_list "@\n  " (fun fmt (i,re) -> Format.fprintf fmt "%i: %a" i pp_rexpr_level re))
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

(*******************************************************************)
(* Commands in input file *)

type cmd =
  | Setting       of setting
  | Problem_Type  of problem_type
  | Arity         of int
  | AddInputs     of input list
  | SetChallenge  of challenge

let pp_cmd fmt cmd =
  match cmd with
  | Setting s       -> F.fprintf fmt "setting %a" pp_setting s
  | Problem_Type pt -> F.fprintf fmt "problem_type %a" pp_problem_type pt
  | Arity a         -> F.fprintf fmt "arity %i" a
  | AddInputs is    -> F.fprintf fmt "addInputs %a" pp_inputs is
  | SetChallenge c  -> F.fprintf fmt "setChallenge %a" pp_challenge c

let handle_cmd cmd assm =
  match cmd with
  | Setting s       ->
    begin match assm.setting with
    | None   -> { assm with setting = Some(s) }
    | Some _ -> failwith "cannot apply 'setting', already set for assumption"
    end
  | Problem_Type pt ->
    begin match assm.problem_type with
    | None   -> { assm with problem_type = Some(pt) }
    | Some _ -> failwith "cannot apply 'problem_type', already set for assumption"
    end
  | Arity a         ->
    begin match assm.arity with
    | None   -> { assm with  arity = Some(a) }
    | Some _ -> failwith "cannot apply 'arity', already set for assumption"
    end
  | AddInputs is    ->
    { assm with inputs = assm.inputs @ is }
  | SetChallenge c  ->
    begin match assm.challenge with
    | None   -> { assm with  challenge = Some(c) }
    | Some _ -> failwith "cannot apply challenge', already set for assumption"
    end

let eval_cmds cmds = List.fold_left (fun assm cmd -> handle_cmd cmd assm) empty_assm cmds 