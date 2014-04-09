open Poly
open Util

module F = Format

(*******************************************************************)
(* Range expressions *)

(* random variable (polynomial in L) *)
type rvar = string

type rlimit_var = int

type ridx_var = int

type level =
  | LevelFixed  of int (* Fixed(i) represents the level i *)
  | LevelOffset of int (* Offset(i) represents the level k - i *)

let pp_level fmt l =
  match l with 
  | LevelFixed i  -> F.fprintf fmt "%i" i
  | LevelOffset i -> F.fprintf fmt "k - %i" i

type exp_var = 
  | Rlimit of rlimit_var  (* l_i *)
  | Ridx   of ridx_var    (* r_i *)
  | Level                 (* k   *)

let pp_exp_var fmt v =
  match v with
  | Rlimit i -> F.fprintf fmt "l%i" i
  | Ridx i   -> F.fprintf fmt "r%i" i
  | Level    -> F.fprintf fmt "k" 

module ExpPoly = MakePoly(struct
  type t = exp_var
  let pp = pp_exp_var
end) (IntRing)

type exp_poly = ExpPoly.t

type pvar = (rvar * exp_poly)

(* assoc lists (FIXME: switch to maps) *)
type input_monomial = pvar list

(* quantifier prefix [ci, li + di] *)
type qprefix = (int * rlimit_var * int) list

type rexpr =
  { re_qprefix        : qprefix;
    re_input_monomial : input_monomial
  }

type input = level * rexpr 

let mk_rexpr pref mon =
  { re_qprefix = pref; re_input_monomial = mon }


(*******************************************************************)
(* Pretty printing *)


let pp_pvar fmt (v,f) =
  if f = ExpPoly.one then
    F.fprintf fmt "%s" v
  else
    F.fprintf fmt "%s^(%a)" v ExpPoly.pp f

let pp_input_monomial fmt f =
  match f with
  | [] -> 
    F.fprintf fmt "1"
  | _  ->
    F.fprintf fmt "%a" (pp_list "*" pp_pvar) f

let pp_qprefix fmt (c,l,d) =
  F.fprintf fmt "[%i,l%i%s]" c l (if d <> 0 then " + "^(string_of_int d) else "")

let pp_range fmt (i,qp) =
  F.fprintf fmt "r%i in %a" i pp_qprefix qp

let pp_rexpr fmt re =
  match re.re_qprefix with
  | [] -> pp_input_monomial fmt re.re_input_monomial
  | qps ->
    F.fprintf fmt "All %a. %a"
      (pp_list "," pp_range) (List.mapi (fun i qp -> (i+1,qp)) qps)
      pp_input_monomial re.re_input_monomial

let pp_rexpr_level fmt (l,re) =
  F.fprintf fmt "%a @@ level %a" pp_rexpr re pp_level l

(*******************************************************************)
(* Testing *)

let bdhe =
  let mk_re qp f = (LevelFixed 1, mk_rexpr qp f) in
  let forall c l d f = mk_re [(c,l,d)] f in
  let l1   = ExpPoly.var (Rlimit 1) in
  let r1   = ExpPoly.var (Ridx 1)   in
  let c i  = ExpPoly.const i in
  let (+)  = ExpPoly.add in
  let (^) s f = [(s,f)] in
  let one = ExpPoly.one in
  let input = 
    [ (* M1 = 1 *)
      mk_re [] []
      (* M2 = Y *)
    ; mk_re [] [("Y",one)] 
      (* M3 = All r1 in [0,l1]. X^r1 *)
    ; forall 0 1 0 ("X"^r1)
      (* M4 = All r1 in [0,l1]. X^(l1 + 1 + r1 *)
    ; forall 0 1 0 ("X" ^ (l1 + (c 2) + r1))
    ]
  in
  let challenge = (LevelFixed 2, ("X"^(l1 + (c 1))) @ ("Y"^(c 1))) in
  F.printf "input: @\n  %a@\n@\n" (pp_list ",@\n  " pp_rexpr_level) input;
  F.printf "challenge: %a @@ level %a\n" pp_input_monomial (snd challenge) pp_level (fst challenge)

(* type rel = 

type constr =
  EqZero (poly 

let find_model (constrs : constr list) =
  Some [("l1",4); ("r_1_1", 5)]

 *)
