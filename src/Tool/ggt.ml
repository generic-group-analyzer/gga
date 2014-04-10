open Poly
open Util

module F = Format

(*******************************************************************)
(* Range expressions *)

(* random variable (assume: polynomials in L are monomials) *)
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
  | Ridx   of ridx_var    (* r_i, de-Bruin-like index starting at 1 for outermost quantifier *)
  | Level                 (* k   *)

let is_Ridx = function Ridx _ -> true | _ -> false

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
      (pp_list "," pp_range) (mapi' (fun i qp -> (i,qp)) qps)
      pp_input_monomial re.re_input_monomial

let pp_rexpr_level fmt (l,re) =
  F.fprintf fmt "%a @@ level %a" pp_rexpr re pp_level l

(*******************************************************************)
(* Constraints *)

module ConstrPoly = MakePoly(struct
  type t = string
  let pp fmt v = F.fprintf fmt "%s" v
end) (IntRing)

type eq_type = Eq | Leq

type constr = ConstrPoly.t * ConstrPoly.t * eq_type * string

let pp_eq_type fmt eqt =
  match eqt with
  | Eq  -> F.fprintf fmt "="
  | Leq -> F.fprintf fmt "<="

let pp_constr fmt (p1,p2,eqt,comment) =
  F.fprintf fmt "%a %a %a \t// %s" ConstrPoly.pp p1 pp_eq_type eqt ConstrPoly.pp p2 comment

let level_to_poly l =
  ConstrPoly.(
    match l with
    | LevelFixed j  -> const j
    | LevelOffset j -> minus (var "k") (const j))

(*******************************************************************)
(* Constraint helper functions *)

let delta_var i = ConstrPoly.var ("delta"^string_of_int i)

let ridx_var i j = ConstrPoly.var (F.sprintf "r_%i_%i" i j)

let rlimit_var i = ConstrPoly.var (F.sprintf "l_%i" i)

let expPoly_to_constrPoly j f =
  let expvar_to_string v =
    match v with
    | Level    -> "k"
    | Rlimit i -> F.sprintf "l_%i" i
    | Ridx   i -> F.sprintf "l_%i_%i" i j
  in
  f
  |> ExpPoly.to_terms
  |> List.map (fun (c,m) -> (c, List.map expvar_to_string m))
  |> ConstrPoly.from_terms

(*******************************************************************)
(* Constraint creation *)

let constr_mult_limit input =
  ConstrPoly.(
    (ladd (mapi' (fun i (l,_) -> mult (level_to_poly l) (delta_var i)) input)
    , var "k"
    , Leq
    , F.sprintf "multiplications bounded by arity"))

let constr_delta_pos input =
  mapi' (fun i _ -> ConstrPoly.(const 0, delta_var i, Leq, F.sprintf "delta_%i positive" i)) input

let constr_range_limits input =
  List.concat
    (mapi'
       (fun j (_l,re) ->
          List.concat
            (mapi'
              (fun i (c,l,d) ->
                 [ ( ConstrPoly.(mult (delta_var j) (const c))
                   , ridx_var i j
                   , Leq
                   , F.sprintf "range variable r_%i in %i-th input monomial, lower bound" i j)
                 ; ( ridx_var i j
                   , ConstrPoly.(mult (delta_var j) (add (rlimit_var l) (const d)))
                   , Leq
                   , F.sprintf "range variable r_%i in %i-th input monomial, upper bound" i j)
                 ])
              re.re_qprefix))
       input)

let constr_degree_equal input (_,c_monomial) =
  let input_monomials : input_monomial list = 
    List.map (fun (_level,re) -> re.re_input_monomial) input 
  in
  let rvars =
    sorted_nub (  List.map fst c_monomial
                @ List.concat (List.map (List.map fst) input_monomials))
  in
  let vdeg_challenge rv =
    try  expPoly_to_constrPoly 0 (List.assoc rv c_monomial)
    with Not_found -> ConstrPoly.const 0
  in
  let vdeg_input rv =
    ConstrPoly.
      (ladd
         (mapi'
            (fun i ms ->
               try
                 let vu  = List.assoc rv ms in
                 let v,u = ExpPoly.partition (fun (_,m) -> List.exists is_Ridx m) vu in
                 (add (expPoly_to_constrPoly i v)
                      (mult (delta_var i) (expPoly_to_constrPoly i u)))
               with Not_found -> const 0)
          input_monomials))
  in
  List.map (fun rv -> (vdeg_challenge rv, vdeg_input rv, Eq, F.sprintf "degree equal for %s" rv)) rvars

let gen_constrs input challenge =
    [ constr_mult_limit input]
  @ constr_delta_pos input
  @ constr_degree_equal input challenge
  @ constr_range_limits input

(*******************************************************************)
(* Tests *)

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
    ; (LevelFixed 2, mk_rexpr [] [("Z1",one)])
    ; (LevelOffset 2, mk_rexpr [] [("Z2",one)])

      (* M3 = All r1 in [0,l1]. X^r1 *)
    ; forall 0 1 0 ("X"^r1)
      (* M4 = All r1 in [0,l1]. X^(l1 + 1 + r1 *)
    ; forall 0 1 0 ("X" ^ (l1 + (c 2) + r1))
    ]
  in
  let challenge = (LevelFixed 2, ("X"^(l1 + (c 1))) @ ("Y"^(c 1))) in
  F.printf "input: @\n  %a@\n@\n"
    (pp_list "@\n  " (fun fmt (i,re) -> Format.fprintf fmt "%i: %a" i pp_rexpr_level re))
    (mapi' (fun i inp -> (i,inp)) input);
  F.printf "challenge: %a @@ level %a\n\n" pp_input_monomial (snd challenge) pp_level (fst challenge);
  F.printf "constrs:\n  %a\n" (pp_list "\n  " pp_constr) (gen_constrs input challenge);
  print_newline ()


