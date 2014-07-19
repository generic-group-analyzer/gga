(*s Synthesize SPS. *)

(*i*)
open Util
open Nondet
open Poly

module IR = IntRing
(*i*)

(* \hd{Generate monomials} *)

(* \ic{We generate all exponent vectors $v$ for a vector $w$ of degree bounds.
       The enumeration algorithm is based on a ranking function that considers
       the vector $v$ as a mixed radix representation of a natural number with
       respect to the radix $w$.} *)

(* \ic{[vec_to_int r v] for the radix $r$ and the vector $v$ returns
       $\Sigma_{i=1}^{|r|} v_i\,(\Pi_{j=1}^{i-1} r_i)$.} *)
let vec_to_int radix v =
  let rec go bs rs i mult =
    match bs,rs with
    | [],[] ->
      i
    | b::bs, r::rs ->
      go bs rs (i + mult*b) (mult*r)
    | _ ->
      failwith "dimensions of given vector and radix vector incompatible"
  in
  go v radix 0 1

(* \ic{[int_to_vec r i] is the inverse of [vec_to_int].} *)
let int_to_vec radix i =
  let rec go i rs v =
    match rs with
    | [] ->
      if i = 0 then Some (L.rev v) else None
    | r::rs ->
      go (i / r) rs ((i mod r)::v)
  in
  go i radix []

(* \ic{Generate all $k$-dimensional vectors $w \in \mathbb{N}^k$ such
       that $k = dim(v)$ and $w_i < v_i$ for all $i$.} *)
let vecs_smaller bvec =
  let rec go i =
    match int_to_vec bvec i with
    | Some v -> mplus (ret v) (go (succ i))
    | None   -> mempty
  in
  go 1

(* \hd{Recipe polynomials} *)

(* \ic{We use the following variables for recipe polynomials.} *)
type recipvar = M | V | W | R | S | One

let string_of_recipvar v = match v with
  | M -> "M" | V -> "V" | W -> "W" | R -> "R" | S -> "S" | One -> "1"

(*i*)
let pp_recipvar fmt v = pp_string fmt (string_of_recipvar v)
(*i*)

(* \ic{Recipe polynomials.} *)
module RecipP = MakePoly(struct
  type t = recipvar
  let pp = pp_recipvar
  let equal = (=)
  let compare = compare
end) (IntRing)

(* \hd{Polynomials with random variables and messages} *)

type rmvar = V_M | V_V | V_W | V_R

(* \ic{We fix this order of random variables for our vector representation.} *)
let varorder = [V_V; V_W; V_R]

let string_of_rmvar v = match v with
  | V_M -> "M" | V_V -> "V" | V_W -> "W" | V_R -> "R"

(*i*)
let pp_rmvar fmt v = pp_string fmt (string_of_rmvar v)
(*i*)

(* \ic{Polynomials with random variables and messages.} *)
module RMP = MakePoly(struct
  type t = rmvar
  let pp = pp_rmvar
  let equal = (=)
  let compare = compare
end) (IntRing)

type rmpoly = RMP.t

(* \hd{Compute verification equation} *)

(* \ic{Simplify [inp] such that non-trivial linear relations are preserved:
       \begin{itemize}
       \item Remove duplicates
       \item Remove polynomials $f = m$ (equal to a monomial) such that
         $m$ does not occur in any other term. We know that they cannot
         included in any non-linear relation.
       \end{itemize}} *)
let simp_inp inp =
  let rec remove_dups left right =
    match right with
    | []                -> L.rev left
    | ((_,r1) as x)::xs ->
      if L.exists (fun (_,r2) -> RecipP.equal r1 r2) left
      then remove_dups left xs
      else remove_dups (x::left) xs
  in
  let not_contains_monom m (p,_) =
    IR.equal (RMP.coeff p m) IR.zero
  in
  let rec remove_unique_monom left right =
    match right with
    | []                  -> L.rev left
    | ((p,_) as x)::right ->
      begin match RMP.mons p with
      | [m] when L.for_all (not_contains_monom m) (left@right) ->
        remove_unique_monom left right
      | _ ->
        remove_unique_monom (x::left) right
      end
  in
  let inp = remove_dups [] inp in
  remove_unique_monom [] inp

(* \ic{Convert list of exponent vectors to [rmpoly].} *)
let evecs_to_poly vs =
  let evec_to_poly v =
    L.combine v varorder
    |> L.map (fun (e,v) -> RMP.pow (RMP.var v) e)
    |> RMP.lmult
  in
  RMP.ladd (L.map evec_to_poly vs)

let verif_eq ?sts s =

  (* \ic{ input in $\group_1$: $[1,V,W,R,S,M]$ } *)
  let inp_g1 =
    [ (RMP.one,     RecipP.var One)
    ; (RMP.var V_V, RecipP.var V)
    ; (RMP.var V_W, RecipP.var W)
    ; (RMP.var V_R, RecipP.var R)
    ; (s,           RecipP.var S)
    ; (RMP.var V_M, RecipP.var M)
    ]
  in

  (* \ic{ input in $\group_2$: $[1,R,S,M]$ } *)
  let inp_g2 =
    [ (RMP.one,     RecipP.var One)
    ; (RMP.var V_R, RecipP.var R)
    ; (s,           RecipP.var S)
    ; (RMP.var V_M, RecipP.var M)
    ]
  in

  (* \ic{ input in $\group_T$: [inp_g1 * inp_g2] minus redundancies } *)
  let inp_gt =
    inp_g1 @
    conc_map
      (fun (f2,r2) -> L.map (fun (f1,r1) -> (RMP.mult f1 f2, RecipP.mult r1 r2)) (L.tl inp_g1))
      (L.tl inp_g2)
  in
  let inp_gt = simp_inp inp_gt in

  (*i F.printf "GT: %a\n" (pp_list ", " (pp_pair RMP.pp RecipP.pp)) inp_gt; i*)
  
  let basis =
    conc_map (fun (p,_) -> RMP.mons p) inp_gt
    |> sorted_nub compare 
  in
  let coeff_vecs = L.map (fun (p,_) -> L.map (RMP.coeff p) basis) inp_gt in
  (*i F.printf "M:=\n";
      F.printf "%a\n" (pp_list "\n" (pp_list " " RMP.pp_coeff)) coeff_vecs; i*)
  let left_kernel = Sage_Solver.compute_kernel ?sts coeff_vecs in
  (*i F.printf "ker:\n%a\n" (pp_list ";\n " (pp_list ", " pp_int)) left_kernel; i*)

  let recip_of_kernel vker =
    L.combine inp_gt vker
    |> L.map (fun ((_,r),c) -> RecipP.(from_int c *@ r))
    |> RecipP.ladd
  in
  L.map recip_of_kernel left_kernel

(* \hd{Analyze Scheme} *)

let synth () =
  let bounds = [2; 2; 3] in
  let max_terms = 2 in
  let i_verif = ref 0 in
  let i_total = ref 0 in
  F.printf "Polynomials for variables %a and bounds %a:\n"
    (pp_list ", " pp_rmvar) varorder
    (pp_list ", " pp_int) bounds;
  let sigs =
    prod (pick_set max_terms (vecs_smaller bounds)) >>= fun (f,g) ->
    guard (f <> []) >>
    ret (f,g)
  in
  let sts = Sage_Solver.start_sage () in
  iter (-1)
    sigs
    (fun (f,g) ->
       incr i_total;
       let f = evecs_to_poly f in
       let g = evecs_to_poly g in
       let s = RMP.(f *@ (var V_M) +@ g) in
       let veqs = verif_eq ~sts s in
       if veqs = [] then (
         F.printf ".%!";
       ) else (
         incr i_verif;
         F.printf "\n%i. S = %a, verif: %a\n%!" !i_verif RMP.pp s
           (pp_list " /\\ " (fun fmt p -> F.fprintf fmt "%a = 0" RecipP.pp p)) veqs
       )
    );
  Sage_Solver.stop_sage sts;
  F.printf "\nChecked %i signature schemes, %i have verification equations" !i_total !i_verif
