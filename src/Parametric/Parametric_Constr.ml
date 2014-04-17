open Poly
open Util
open Parametric_Input

module F = Format

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

let expvar_to_string j v =
  match v with
  | Level                -> "k"
  | Rlimit i when i = -1 -> F.sprintf "l"
  | Rlimit i             -> F.sprintf "l_%i" i
  | Ridx   s             -> F.sprintf "%s_%i" s j

let delta_var i = ConstrPoly.var ("d_"^string_of_int i)

let ridx_var s j = ConstrPoly.var (expvar_to_string j (Ridx s))

let rlimit_var i = ConstrPoly.var (expvar_to_string 0 (Rlimit i))

let expPoly_to_constrPoly j f =
  f
  |> ExpPoly.to_terms
  |> List.map (fun (c,m) -> (c, List.map (expvar_to_string j) m))
  |> ConstrPoly.from_terms

(*******************************************************************)
(* Constraint creation *)

let constr_mult_limit input =
    ConstrPoly.(
    (ladd (mapi' (fun i (l,_) -> mult (level_to_poly l) (delta_var i)) input)
    , var "k"
    , Eq
    , F.sprintf "multiplications bounded by challenge level"))

let constr_delta_pos input =
  mapi' (fun i _ -> ConstrPoly.(const 0, delta_var i, Leq, F.sprintf "delta_%i positive" i)) input

let constr_range_limits input =
  List.concat
    (mapi'
       (fun j (_l,re) ->
          List.concat
            (List.map
              (fun (s,(c,l,d)) ->
                 [ ( ConstrPoly.(mult (delta_var j) (const c))
                   , ridx_var s j
                   , Leq
                   , F.sprintf "lower bound for range variable %s in input monomial %i" s j)
                 ; ( ridx_var s j
                   , ConstrPoly.(mult (delta_var j) (add (rlimit_var l) (const d)))
                   , Leq
                   , F.sprintf "upper bound for range variable %s in input monomial %i" s j)
                 ; ( ConstrPoly.const 0
                   , ConstrPoly.(add (rlimit_var l) (const d))
                   , Leq
                   , F.sprintf "upper bound non-negative for range variable %s in input monomial %i" s j)
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
    constr_delta_pos input
  @ constr_range_limits input
  @ [ constr_mult_limit input]
  @ constr_degree_equal input challenge
  @ [ (level_to_poly (LevelOffset 0), level_to_poly (fst challenge), Eq, "assume challenge on highest level") ]
