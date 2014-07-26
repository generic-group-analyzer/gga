(*s Synthesize SPS. *)

(*i*)
open Util
open Nondet
open LPoly
open LStringPoly
open InteractiveAnalyze

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
  go 0

(* \hd{Recipe polynomials} *)

(* \ic{We use the following variables for recipe polynomials.} *)
type recipvar = M | V | W | R | S | One

let string_of_recipvar v = match v with
  | M -> "wM" | V -> "V" | W -> "W" | R -> "wR" | S -> "wS" | One -> "1"

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
       \item Remove polynomials $f$ containing a monomial $m$ such that
         $m$ does not occur in any other polynomial. We know that they cannot
         be included in any non-trivial linear relation.
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
  let monom_unique ps m =
    L.for_all (not_contains_monom m) ps
  in
  let rec remove_unique_monom left right =
    match right with
    | []                  -> L.rev left
    | ((p,_) as x)::right ->
      begin match RMP.mons p with
      | _::_ as ms when L.exists (monom_unique (left@right)) ms ->
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
    |> L.map (fun (e,v) -> RMP.var_exp v ( e - 1 )) (* also generate negative exponents *)
    |> RMP.lmult
  in
  RMP.ladd (L.map evec_to_poly vs)

(* \ic{Compute verification equation.} *)
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

let to_gdef s veqs =
  fsprintf
    ("map G1 * G2 -> GT.\n"^^
     "iso G2 -> G1.\n"^^
     "input [V,W] in G1.\n"^^
     "oracle o1(M:G2) =\n"^^
     "  sample R;\n"^^
     "  return [ R, %a ] in G2.\n"^^
     "\n"^^
     "win (wM:G2, wR:G2, wS:G2) = (wM <> M /\\ 0 = %a).\n")
    RMP.pp s
    (pp_list " /\\ 0 = " RecipP.pp) veqs

let to_gdef_sigrand s veqs =
  let rename v = match v with
    | V_M -> SP.var "sM"
    | V_R -> SP.var "sR"
    | _   -> SP.var (string_of_rmvar v)
  in
  fsprintf
    ("map G1 * G2 -> GT.\n"^^
     "iso G2 -> G1.\n"^^
     "input [V,W] in G1.\n"^^
     "input [ sR, sM, %a ] in G2.\n"^^
     "oracle o1(M:G2) =\n"^^
     "  sample R;\n"^^
     "  return [ R, %a ] in G2.\n"^^
     "\n"^^
     "win (wM:G2, wR:G2, wS:G2) = (wM <> M /\\ wM <> sM /\\ 0 = %a).\n")
    SP.pp (RMP.to_terms s |> SP.eval_generic SP.const rename)
    RMP.pp s
    (pp_list " /\\ 0 = " RecipP.pp) veqs

let synth () =
  let bounds = [3; 3; 4] in
  let max_terms = 2 in
  let offset v = List.map (fun x -> x - 1) v in
  let i_verif   = ref 0 in
  let i_total   = ref 0 in
  let i_secure  = ref 0 in
  let i_unknown = ref 0 in
  let i_attack  = ref 0 in
  let deg_vec v = L.nth v 0 + L.nth v 1 + L.nth v 2 in
  let deg_vec_vw v = L.nth v 0 + L.nth v 1 in

  F.printf "Polynomials for variables %a and bounds %a <= v < %a:\n"
    (pp_list ", " pp_rmvar) varorder
    (pp_list ", " pp_int) (offset [ 0; 0; 0 ])
    (pp_list ", " pp_int) bounds;
  let sig_uses_sk f g =
    L.exists (fun v -> let v = offset v in deg_vec_vw v > 0) (f@g)
  in
  let sym_minimal f g =
    let swap_v_w m = match m with
      | [ x; y; z ] -> [ y; x; z]
      | _ -> failwith "impossible"
    in
    compare (L.map swap_v_w f,L.map swap_v_w g) (f,g) >= 0
  in
  let vecs =
    vecs_smaller bounds >>= fun vo ->
    let v = offset vo in
    guard (   (*i the monomial cannot be v^(0,0,0) = 1 i*)
              v <> [ 0; 0; 0 ]
              (*i Since V and W are in G1, V*W cannot be computed in GT i*)
           && not (L.nth v 0 + L.nth v 1 > 1)
          ) >>
    ret vo
  in
  let vecs_f =
    vecs >>= fun v ->
    guard (   (* We cannot check a signature with terms of degree > 1 for any
                 of the variables since M consumes already one degree in the
                 verification equation *)
              let v = offset v in deg_vec v < 2
          ) >>
    ret v
  in
  let vecs_g =
    vecs >>= fun v ->
    guard (  let v = offset v in 
             (* g cannot be of the form h + r since the smaller signature h
                is equivalent wrt. to security (adversary can add/remove R to S) *)
              (v <> [ 0; 0; 1])
              (* not completely clear: at most one one multiplication *)
           && (deg_vec v <= 2)
          ) >>
    ret v
  in
  let sigs =
    cart (pick_set max_terms vecs_f) (pick_set max_terms vecs_g) >>= fun (f,g) ->
    guard (   (* this is 0 *)
              f <> []
              (* the signature must use either V or W *)
           && sig_uses_sk f g
              (* symmetry reduction, we choose (the smaller signature) in the
                 equivalence class obtained by renaming V to W *)
           && sym_minimal f g) >>
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
         F.printf "%i %!" !i_total
       ) else (
         incr i_verif;
         let sgdef = to_gdef s veqs in
         let res = analyze_bounded_from_string ~counter:true ~fmt:null_formatter sgdef 1 in
         match res with
         | Z3_Solver.Valid ->
           incr i_secure;
           F.printf "\n%i. S = %a, verif: %a\n%!" !i_secure RMP.pp s
             (pp_list " /\\ " (fun fmt p -> F.fprintf fmt "%a = 0" RecipP.pp p)) veqs;
           output_file (F.sprintf "./gen/%02i.ec" !i_secure) sgdef;
           output_file (F.sprintf "./gen/%02i_sigrand.ec" !i_secure) (to_gdef_sigrand s veqs)
         | Z3_Solver.Unknown -> 
           F.printf "\n%i? %!\n" !i_total;
           incr i_unknown
         | Z3_Solver.Attack _ ->
           output_file (F.sprintf "./gen/attack/%02i_attack.ec" !i_attack) sgdef;
           F.printf "\n%i! %!\n" !i_total;
           incr i_attack;
         | Z3_Solver.Error e ->
           F.printf "Error: %s\n" e;
           incr i_unknown
       )
    );
  Sage_Solver.stop_sage sts;
  F.printf
    "\n%i Checked: %i no verification equation / %i secure / %i attack / %i unknown\n"
    !i_total (!i_total - !i_verif) !i_secure !i_attack  !i_unknown
