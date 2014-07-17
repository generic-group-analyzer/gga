(*s Bounded analysis for interactive assumptions. *)

open Util
open Poly

module II = InteractiveInput
module RP = II.RP
module WP = II.WP
module OP = II.OP

type query_idx = int

(* Coefficient index: the j-th coefficient in linear combination of terms *)
type coeff_idx = int

(* \begin{itemize}
   \item for sampled shared variables: $V,W$
   \item for variables sampled in oracles: $R_1,..,R_q$
   \end{itemize}
*)
type rvar =
  | SRVar of II.id
  | ORVar of II.id * query_idx

let string_of_rvar r = match r with
  | SRVar i      -> i
  | ORVar (i, q) -> F.sprintf "%s_%i" i q

let pp_rvar fmt r = pp_string fmt (string_of_rvar r)

(* \begin{itemize}
   \item $m$ in LRSW
   \item $\alpha^{M}_{i,j}$: coefficient of $j$-th element in the completion
      (for the right group) before calling the oracle the $i$-time.
  \item $mm$ in LRSW
  \item $\beta^{M'}_j$: coefficient of $j$-th element in the completion
      after performing the last oracle call.
  \end{itemize}
*)
type param =
  | FOParam of II.id * query_idx
  | OCoeff  of II.id * query_idx * coeff_idx
  | FChoice of II.id
  | ChoiceCoeff of II.id * coeff_idx

let string_of_param p = match p with
  | FOParam (id, q)     -> F.sprintf "%s_%i" id q
  | OCoeff  (id, q, i)  -> F.sprintf "%s_%i_%i" id q i
  | FChoice id          -> id
  | ChoiceCoeff (id, i) -> F.sprintf "%s_%i" id i

let pp_param fmt p = pp_string fmt (string_of_param p)

(****************************************************
 *************** Compute completion *****************
 ****************************************************)

type var =
  | RVar of rvar
  | Param of param

let pp_var fmt v = match v with
  | RVar r -> pp_rvar fmt r
  | Param p -> pp_param fmt p

module GP = MakePoly(struct
  type t      = var
  let pp      = pp_var
  let equal   = (=)
  let compare = compare
end) (IntRing)

let make_fresh_var_gen s q =
  let i = ref 0 in
  function () -> i := !i+1;
                 GP.var (Param (OCoeff (s, q, !i)))

let lin_comb_of_gps ps cgen =
  L.fold_left (fun acc p -> GP.add acc (GP.mult (cgen ()) p))
              GP.zero
              ps

let ovar_to_gp cur q v =
  match v with
  | II.SRVar r -> GP.var (RVar (SRVar r))
  | II.ORVar r -> GP.var (RVar (ORVar (r, q)))
  | II.Param t -> if t.II.tid_ty = II.Field
                  then GP.var (Param (FOParam (t.II.tid_id, q)))
                  else lin_comb_of_gps cur
                       (make_fresh_var_gen (F.sprintf "[%s]" t.II.tid_id) q)


(* cur is the currently computable polynomials, f is an opoly
  returned by an oracle query *)
let complete_polynomial cur q f =
  let translate_term t =
    let factors = L.map (ovar_to_gp cur q) (fst t) in
    let coeff = GP.const (snd t) in
    GP.mult (GP.lmult factors)
            coeff
  in 
  f |> OP.to_terms
    |> L.map translate_term
    |> GP.ladd

let compute_completion cur o bound =
  let rec loop i cur =
    if i > bound then cur
    else L.map fst o.II.odef_return
         |> L.map (complete_polynomial cur i)
         |> (@) cur 
         |> loop (i+1) 
  in
  loop 1 cur


(****************************************************
 *************** Extract coefficients ***************
 ****************************************************)

module CP = MakePoly(struct
  type t      = param
  let pp      = pp_param
  let equal   = (=)
  let compare = compare
end) (IntRing)

module CPR = struct
  type t         = CP.t
  let pp         = CP.pp
  let add        = CP.add
  let opp        = CP.opp
  let mult       = CP.mult
  let ring_exp   = CP.ring_exp
  let one        = CP.one
  let zero       = CP.zero
  let ladd       = CP.ladd
  let from_int   = CP.from_int
  let equal      = CP.equal
  let compare    = CP.compare
  let use_parens = true
end

module EP = MakePoly(struct
  type t      = rvar
  let pp      = pp_rvar
  let equal   = (=)
  let compare = compare
end) (CPR)

let is_rvar f = match f with | RVar _ -> true | _ -> false

let gp_to_ep p =
  let cconv i = EP.const (CP.const i) in
  let vconv v = match v with
    | RVar r  -> EP.var r
    | Param p -> EP.const (CP.var p)
  in
  GP.to_terms p |> EP.eval_generic cconv vconv

let extract_constraints p =
  gp_to_ep p |> EP.to_terms |> L.map snd

let cp_to_rpoly p =
  let cconv c = RP.const c in
  let vconv v = RP.var (string_of_param v) in
  CP.to_terms p |> RP.eval_generic cconv vconv

(****************************************************
 *************** Extract constraints ****************
 ****************************************************)

let rpoly_to_gp p =
  let cconv i = GP.const i in
  let vconv v = GP.var (RVar (SRVar v)) in
  RP.to_terms p |> GP.eval_generic cconv vconv

let cgen s =
  let i = ref 0 in
  function () ->
    i := !i+1;
    GP.var (Param (ChoiceCoeff (s, !i)))

let nonquant_wp_to_gp cur p =
  let cconv c = GP.const c in
  let vconv v = match v with
    | II.RVar id    -> GP.var (RVar (SRVar id))
    | II.OParam _   -> failwith "Called with quantified winning condition."
    | II.Choice tid -> if tid.II.tid_ty = Field
                       then GP.var (Param (FChoice(tid.II.tid_id)))
                       else lin_comb_of_gps cur (cgen (F.sprintf "C_%s" tid.II.tid_id))
  in
  WP.to_terms p |> GP.eval_generic cconv vconv

let quant_wp_to_gps cur bound p =
  let ps = L.map (fun _ -> p) (list_from_to 1 bound) in
  let q = ref 0 in
  let cconv c = GP.const c in
  let vconv v = match v with
    | II.RVar id    -> GP.var (RVar (SRVar id))
    | II.OParam tid -> if tid.II.tid_ty = Field
                       then GP.var (Param (FOParam (tid.II.tid_id, !q)))
                       else GP.var (Param (FOParam ("FIXME", !q)))
                       (* else failwith "Oracle handles in winning condition not supported!" *)
    | II.Choice tid -> if tid.II.tid_ty = Field
                       then GP.var (Param (FChoice(tid.II.tid_id)))
                       else lin_comb_of_gps cur (cgen (F.sprintf "C_%s" tid.II.tid_id))
  in  
  L.map (fun p -> q := !q + 1; WP.to_terms p |> GP.eval_generic cconv vconv) ps

(* Checks if a wpoly is quantified, i.e. contains oracle parameters *)
let is_quantified f =
  let is_qvar v = match v with | II.OParam _ -> true | _ -> false in
  L.fold_left (fun acc v -> acc || is_qvar v) false (WP.vars f)

let gdef_to_constrs b gdef =
  (* Compute the completion of the input w.r.t. b oracle calls *)  
  let cur = L.map rpoly_to_gp gdef.II.gdef_inputs in
  let comp = compute_completion cur (L.hd gdef.II.gdef_odefs) b in
  F.printf "%a\n" (pp_list "\n" GP.pp) comp;

  let eqs = gdef.II.gdef_wcond.II.wcond_eqs in
  let ineqs = gdef.II.gdef_wcond.II.wcond_ineqs in
  let (qeqs, eqs) = L.partition is_quantified eqs in
  let (qineqs, ineqs) = L.partition is_quantified ineqs in

  F.printf "############ Equalities ###########\n";
  F.printf "%a\n" (pp_list "\n" WP.pp) eqs;
  F.printf "\n############ Quantified Equalities ###########\n";
  F.printf "%a\n" (pp_list "\n" WP.pp) qeqs;
  F.printf "\n############ Inequalities ###########\n";
  F.printf "%a\n" (pp_list "\n" WP.pp) ineqs;
  F.printf "\n############ Quantified Inequalities ###########\n";
  F.printf "%a\n" (pp_list "\n" WP.pp) qineqs;

  if qeqs <> [] then failwith "Only inequalities can contain oracle parameters.";

  (* Expand winning conditions based on number of oracle queries *)
  F.printf "\n############ Unrolled Inequalities ###########\n";
  let qineqs = conc_map (quant_wp_to_gps comp b) qineqs in
  F.printf "%a\n" (pp_list "\n" GP.pp) qineqs;

  let eqs = L.map (nonquant_wp_to_gp comp) eqs in
  let ineqs = L.map (nonquant_wp_to_gp comp) ineqs in

  (* Substitute group variables with their possible values *)

  F.printf "\n############ Equalities for constraint generation ###########\n";
  F.printf "0 = %a\n" (pp_list "\n\n0 = " EP.pp) (L.map gp_to_ep eqs);

  F.printf "\n############ Inequalities for constraint generation ###########\n";
  F.printf "0 <> %a\n" (pp_list "\n\n0 <> " EP.pp) (L.map gp_to_ep ineqs);

  let eqs_constrs = conc_map extract_constraints eqs in

  F.printf "\n############## Equality constraints ##############\n";
  F.printf "0 = %a\n" (pp_list "\n\n0 = " RP.pp) (L.map cp_to_rpoly eqs_constrs);

  let ineqs_constrs = L.map extract_constraints (ineqs @ qineqs) in

  F.printf "\n############## Inequality constraints ##############\n";
  List.iter (fun fs ->
               F.printf "%a\n" (pp_list " \\/ " (fun fmt f -> F.fprintf fmt "%a <> 0" RP.pp f)) fs)
             (L.map (fun f -> L.map cp_to_rpoly f) ineqs_constrs);
  
  (L.map cp_to_rpoly eqs_constrs, L.map (fun f -> L.map cp_to_rpoly f) ineqs_constrs)