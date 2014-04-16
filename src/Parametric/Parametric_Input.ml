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
  | Rlimit i -> F.fprintf fmt "l%i" i
  | Ridx v   -> F.fprintf fmt "%s" v
  | Level    -> F.fprintf fmt "k" 

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
  F.fprintf fmt "[%i,l%i%s]" c l (if d <> 0 then " + "^(string_of_int d) else "")

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
