open Util

module F = Format

(*******************************************************************)
(* Range expressions *)

type rvar = string

type rlimit_var = int

type ridx_var = int

type level =
  | Fixed  of int (* Fixed(i) represents the level i *)
  | Offset of int (* Offset(i) represents the level k - i *)

type exp_var = 
  | Rlimit of rlimit_var  (* l_i *)
  | Ridx   of ridx_var    (* r_i *)
  | Level                 (* k   *)

type exp_monom = exp_var list

type exp_poly = (int * exp_monom) list

(* considered as assoc lists, maybe switch to maps later *)
type poly = (rvar * exp_poly) list

(* quantifier prefix [ci, li + di] *)
type qprefix = (int * rlimit_var * int) list

type rexpr =
  { re_qprefix : qprefix;
    re_poly    : poly
  }

type input = level * rexpr 

let mk_rexpr pref poly =
  { re_qprefix = pref; re_poly = poly }

(*******************************************************************)
(* Pretty printing *)

let pp_level fmt l =
  match l with 
  | Fixed i  -> F.fprintf fmt "%i" i
  | Offset i -> F.fprintf fmt "k - %i" i

let pp_exp_var fmt v =
  match v with
  | Rlimit i -> F.fprintf fmt "l%i" i
  | Ridx i   -> F.fprintf fmt "r%i" i
  | Level    -> F.fprintf fmt "k" 

let pp_exp_monom fmt m =
  F.fprintf fmt "%a" (pp_list "*" pp_exp_var) m

let pp_exp_term fmt (c,m) =
  if m = [] then F.fprintf fmt "%i" c
  else if c = 1 then pp_exp_monom fmt m
  else F.fprintf fmt "%i %a" c pp_exp_monom m

let pp_exp_poly fmt f =
  F.fprintf fmt "%a" (pp_list "+" pp_exp_term) f

let pp_pvar fmt (v,f) =
  match f with
  | [] ->
    F.fprintf fmt "%s" v
  | _  -> 
    F.fprintf fmt "%s^(%a)" v pp_exp_poly f

let pp_poly fmt f =
  match f with
  | [] -> 
    F.fprintf fmt "1"
  | _  ->
    F.fprintf fmt "%a" (pp_list " " pp_pvar) f

let pp_qprefix fmt (c,l,d) =
  F.fprintf fmt "[%i,l%i + %i]" c l d

let pp_range fmt (i,qp) =
  F.fprintf fmt "r%i in %a" i pp_qprefix qp

let pp_rexpr fmt re =
  match re.re_qprefix with
  | [] -> pp_poly fmt re.re_poly
  | qps ->
    F.fprintf fmt "All %a. %a"
      (pp_list "," pp_range) (List.mapi (fun i qp -> (i+1,qp)) qps)
      pp_poly re.re_poly

let pp_rexpr_level fmt (l,re) =
  F.fprintf fmt "%a @@ level %a" pp_rexpr re pp_level l

(*******************************************************************)
(* Testing *)

let bdhe =
  let mk_re qp f = (Fixed 1, mk_rexpr qp f) in
  let forall c l d f = mk_re [(c,l,d)] f in
  let l1   = [(1,[Rlimit 1])] in
  let r1   = [(1,[Ridx 1])]   in
  let c i = [(i,[])] in
  let (+) = (@) in
  let (^) s f = [(s,f)] in
  let input = 
    [ (* M1 = 1 *)
      mk_re [] []
      (* M2 = Y *)
    ; mk_re [] [("Y",[])] 
      (* M3 = All r1 in [0,l1]. X^r1 *)
    ; forall 0 1 0 ("X"^r1)
      (* M4 = All r1 in [0,l1]. X^r1 *)
    ; forall 0 1 0 ("X" ^ (l1 + (c 2) + r1))
    ]
  in
  let challenge = (Fixed 2, ("X"^(l1 + (c 1))) @ ("Y"^(c 1))) in
  F.printf "input: @\n  %a@\n@\n" (pp_list ",@\n  " pp_rexpr_level) input;
  F.printf "challenge: %a @@ level %a\n" pp_poly (snd challenge) pp_level (fst challenge)

