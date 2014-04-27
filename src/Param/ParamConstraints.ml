(*s Generation of constraints for parametric problems. *)
(*i*)
open Poly
open Util
open ParamInput
(*i*)


(*******************************************************************)
(* \hd{Constraints} *)

(* \ic{We use strings as variables for constraint polyomials.} *)
module CP = MakePoly(
  struct
    type t = string
    let pp = pp_string
    let equal = (=)
    let compare = compare
  end) (IntRing)

(* \ic{A constraint either represents $a = b$ or $a \leq b$.} *)
type constr_type = Eq | Leq

(* \ic{We associate an information string with a constraint.} *)
type constr = CP.t * constr_type * CP.t * string

(*******************************************************************)
(* \hd{Constraint helper functions} *)

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
let ep_to_cp ?inum:(j=0) f =
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
let l_to_cp l =
  CP.(match l with LevelFixed j -> from_int j | LevelOffset j -> var "k" -@ from_int j)

(*******************************************************************)
(* \hd{Constraint generation} *)

(* \input{constraint_generation} *)

(*******************************************************************)
(* \newpage\hd{Constraint generation implementation} *)

(* \\
   Instead of computing $(I_1^{\delta_1} * \ldots * I_b^{\delta_n})$
   explicitly, we compute the polynomials $f_i$ in $(4)$
   on the fly and make the range indices $I_j$ distinct from range indices
   in other inputs by appending~$j$. *)

(* \ic{Create the constraints $0 \leq \delta_i$. \quad $(2.2)$} *)
let constr_delta_pos input =
  mapi'
    (fun i _ -> CP.(from_int 0 , Leq, delta_var i, F.sprintf "delta_%i non-negative" i))
    input

(* \ic{Create the constraint
       $\Sigma_{i=1}^n \, \delta_i * \lambda_i = \lambda$.\quad $(2.3)$} *)
let constr_mult_limit input chal_l =
  let msg = "multiplications yield result on challenge level" in
  let sum = CP.(ladd (mapi' (fun i (l,_) -> l_to_cp l *@ delta_var i) input)) in
  match chal_l with
  | LevelFixed j  -> [ CP.( sum , Eq, from_int j, msg) ]

  (* \ic{Z3 prefers an Equation of the form e - i = k to e = k - i} *)
  | LevelOffset j -> [ CP.( sum +@ from_int j, Eq, var "k", msg) ]


(* \ic{Create the constraints $\delta_i * \alpha_{i,j} \leq r$,
       $r \leq \delta_i * \beta_{i,j}$, and $\alpha_j \leq \beta_j$.
       \quad $(2.4)$ and $(2.1)$} *)
let constr_range_limits input =
  let gen_constr j (s,(a,b)) =
    CP.(
      [ ( delta_var j *@ ep_to_cp a, Leq, ridx_var j s
        , F.sprintf "lower bound for range variable %s in input %i" s j)
      ; ( ridx_var j s, Leq, delta_var j *@ ep_to_cp b
        , F.sprintf "upper bound for range variable %s in input %i" s j)
      ; ( ep_to_cp a, Leq, ep_to_cp b
        , F.sprintf "range for variable %s in input %i increasing and non-empty" s j)
      ])
  in
  L.concat
    (mapi' (fun j (_l,re) -> conc_map (gen_constr j) re.re_qprefix) input)

(* \ic{Create constraints $i < k$ for all such levels in assumption. \quad $(2.5)$.} *)
let constr_levels input chal_level =
  let offset_of_level = function LevelOffset i -> [i] | LevelFixed  _ -> [] in
  let constr_of_offset i =
    CP.(from_int (i + 1), Leq, var "k", "All levels must be >= 1")
  in
  chal_level::(L.map fst input)
    |> conc_map offset_of_level
    |> sorted_nub compare
    |> L.map constr_of_offset

(* \ic{%
   Create the constraints $f_i = g_i$. \quad $(2.6)$ \\
   We compute $f_i$ as $\Sigma_{j=1}^n (\xi_{i,j} + \delta_j * \psi_{i,j})$
   where $\xi_{i,j}$ is the sum of all terms of $f_{j,i}$
   (exponent of $X_i$ in input $I_j$) that contain a range index and
   $\psi_{i,j}$ is the sum of all terms that do not.
   } *)
let constr_degree_equal input c_monomial =
  let input_monomials = L.map (fun (_,re) -> re.re_input_monomial) input in
  let rvars =
    sorted_nub compare
      (L.map fst c_monomial @ conc_map (L.map fst) input_monomials)
  in
  let vdeg_challenge rv =
    try ep_to_cp (L.assoc rv c_monomial) with Not_found -> CP.from_int 0
  in
  let vdeg_input rv =
    CP.
      (ladd
         (mapi'
            (fun j ms ->
               try
                 let xi_psi  = L.assoc rv ms in
                 let xi,psi = EP.partition (fun (m,_) -> L.exists is_Ridx m) xi_psi in
                 (ep_to_cp ~inum:j xi +@ (delta_var j *@ ep_to_cp ~inum:j psi))
               with Not_found -> from_int 0)
            input_monomials))
  in
  L.map
    (fun rv -> (vdeg_challenge rv, Eq, vdeg_input rv, F.sprintf "degree equal for %s" rv))
    rvars

(* \ic{Create arity constraint if specified.} *)
let constr_arity arity =
  match arity with
  | Some i -> [ CP.(from_int i, Eq, var "k", "Arity fixed in assumption") ]
  | None   -> []

(* \ic{Create constraints $(2.1)$--$(2.5)$ and constraint for arity} *)   
let gen_constrs _problem_type input challenge arity =
    constr_delta_pos input
  @ constr_mult_limit input challenge.chal_level
  @ constr_range_limits input
  @ constr_degree_equal input challenge.chal_input_monomial
  @ constr_levels input challenge.chal_level
  @ constr_arity arity

(*i*)
(*******************************************************************)
(* \hd{Pretty printing} *)

let pp_eq_type fmt eqt =
  match eqt with
  | Eq  -> F.fprintf fmt "="
  | Leq -> F.fprintf fmt "<="

let pp_constr fmt (p1,eqt,p2,comment) =
  F.fprintf fmt "%a %a %a \t// %s" CP.pp p1 pp_eq_type eqt CP.pp p2 comment

(*i*)
