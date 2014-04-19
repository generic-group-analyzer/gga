(*s Generation of constraints for parametric problems. *)
(*i*)
open Poly
open Util
open ParametricInput
(*i*)


(*******************************************************************)
(* \subsection*{Constraints} *)

(* \ic{We use strings as variables for constraint polyomials.} *)
module CP = MakePoly(struct
  type t = string
  let pp fmt v = F.fprintf fmt "%s" v
end) (IntRing)

(* \ic{A constraint either represents $a = b$ or $a \leq b$.} *)
type constr_type = Eq | Leq

(* \ic{We associate an information string with a constraint.} *)
type constr = CP.t * CP.t * constr_type * string

(*******************************************************************)
(* \subsection*{Constraint helper functions} *)

(* \ic{[ev_to_cv j ev] translates the exponent variable [ev] into a
   constraint variable. It uses [j] to make range indices used in
   the different inputs distinct.} *)
let ev_to_cv j v =
  match v with
  | Level                -> "k"
  | Rlimit i when i = -1 -> F.sprintf "l"
  | Rlimit i             -> F.sprintf "l_%i" i
  | Ridx   s             -> F.sprintf "%s_%i" s j

(* \ic{[ep_to_cp j ep] translates the exponent polyomial [ep] occuring in the
   into a constraint polynomial. It uses [j] to make range indices used in
   the different inputs distinct.} *)
let ep_to_cp j f =
  f
  |> EP.to_terms
  |> L.map (fun (m,c) -> (L.map (ev_to_cv j) m, c))
  |> CP.from_terms

(* \ic{Create constraint polynomial for [Ridx] variabe in [j]-th input.} *)
let ridx_var j s = CP.var (ev_to_cv j (Ridx s))

(* \ic{Create constraint polynomial for [Rlimit] variable.} *)
let rlimit_var i = CP.var (ev_to_cv 0 (Rlimit i))

(* \ic{Create $\delta_j$ variable for $j$-th input (see explanation below).} *)
let delta_var j = CP.var ("d_"^string_of_int j)

(* \ic{We translate levels to constraint polynomials in the expected way.} *)
let level_to_cp l =
  CP.(match l with
      | LevelFixed j  -> const j
      | LevelOffset j -> (var "k") -@ (const j))

(*******************************************************************)
(* \subsection*{Constraint generation} *)

(* \input{constraint_generation} *)

(*******************************************************************)
(* \newpage\subsection*{Constraint generation implementation} *)

(* \ic{%
   Instead of computing $(I_1^{\delta_1} * \ldots * I_b^{\delta_n})$
   explicitly, we compute the polynomials $f_i$ in $(4)$
   on the fly and make the range indices $I_j$ distinct from range indices
   in other inputs by appending~$j$.}
*)

(* \ic{Create the constraints $0 \leq \delta_i$. \quad $(2)$} *)
let constr_delta_pos input =
  mapi'
    (fun i _ -> CP.(const 0, delta_var i, Leq, F.sprintf "delta_%i positive" i))
    input

(* \ic{Create the constraint
       $\Sigma_{i=1}^n \, \delta_i * \lambda_i = \lambda$.\quad $(3)$} *)
let constr_mult_limit input (chal_level, _) =
    CP.(
    (ladd (mapi' (fun i (l,_) -> level_to_cp l *@ delta_var i) input)
    , level_to_cp chal_level
    , Eq
    , F.sprintf "multiplications bounded by challenge level"))


(* \ic{Create the constraints $\delta_i * \alpha_{i,j} \leq r$,
       $r \leq \delta_i * \beta_{i,j}$, and $\alpha_j+1 \leq \beta_j$.
       \quad $(4)$ and $(1)$} *)
let constr_range_limits input =
  let gen_constr j (s,(a,b)) =
    CP.(
      [ ( delta_var j *@ ep_to_cp 0 a
        , ridx_var j s
        , Leq
        , F.sprintf "lower bound for range variable %s in input %i" s j)
      ; ( ridx_var j s
        , delta_var j *@ ep_to_cp 0 b
        , Leq
        , F.sprintf "upper bound for range variable %s in input %i" s j)
      ; ( ep_to_cp 0 a +@ const 1
        , ep_to_cp 0 b
        , Leq
        , F.sprintf "range for variable %s in input %i increasing and non-empty" s j)
      ])
  in
  L.concat
    (mapi' (fun j (_l,re) -> conc_map (gen_constr j) re.re_qprefix) input)

(* \ic{%
   Create the constraints $f_i = g_i$. \quad $(4)$ \\
   We compute $f_i$ as $\Sigma_{j=1}^n (\xi_{i,j} + \delta_j * \psi_{i,j})$
   where $\xi_{i,j}$ consists of all terms of $f_{j,i}$ (used in the input $I_j$)
   that contain some variable in $\vec{r}_j$ and $\psi_{i,j}$ of all terms that do not.
   } *)
let constr_degree_equal input (_,c_monomial) =
  let input_monomials = L.map (fun (_,re) -> re.re_input_monomial) input in
  let rvars = sorted_nub (L.map fst c_monomial @ conc_map (L.map fst) input_monomials) in
  let vdeg_challenge rv =
    try ep_to_cp 0 (L.assoc rv c_monomial) with Not_found -> CP.const 0
  in
  let vdeg_input rv =
    CP.
      (ladd
         (mapi'
            (fun j ms ->
               try
                 let xi_psi  = L.assoc rv ms in
                 let xi,psi = EP.partition (fun (m,_) -> L.exists is_Ridx m) xi_psi in
                 (ep_to_cp j xi +@ (delta_var j *@ ep_to_cp j psi))
               with Not_found -> const 0)
            input_monomials))
  in
  L.map
    (fun rv -> (vdeg_challenge rv, vdeg_input rv, Eq, F.sprintf "degree equal for %s" rv))
    rvars

(* \ic{Compute constraints $(1)$--$(4)$.} *)   
let gen_constrs input challenge =
    constr_delta_pos input
  @ [ constr_mult_limit input challenge ]
  @ constr_range_limits input
  @ constr_degree_equal input challenge

(*i*)
(*******************************************************************)
(* \subsection*{Pretty printing} *)

let pp_eq_type fmt eqt =
  match eqt with
  | Eq  -> F.fprintf fmt "="
  | Leq -> F.fprintf fmt "<="

let pp_constr fmt (p1,p2,eqt,comment) =
  F.fprintf fmt "%a %a %a \t// %s" CP.pp p1 pp_eq_type eqt CP.pp p2 comment

(*i*)
