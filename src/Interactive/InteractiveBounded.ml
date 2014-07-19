(*s Bounded analysis for interactive assumptions. Consists of three
    steps:
    \begin{itemize}
    \item Compute symbolic completion wrt. isos, maps, and oracle queries.
    \item Make winning condition handle-free and extract constraints.
    \item Call Sage to solve constraints.
    \end{itemize}
*)

(*i*)
open Util
open Poly

module II = InteractiveInput
module RP = II.RP
module WP = II.WP
module OP = II.OP
(*i*)

(*i ********************************************************************* i*)
(* \hd{Polynomials with parameters and random variables} *)
(*i ********************************************************************* i*)


(* \ic{The index of an oracle query, between $1$ and the bound $q$.} *)
type query_idx = int

(* \ic{Coefficient index: the $j$-th coefficient in linear combination of polynomials.} *)
type coeff_idx = int

(* \ic{Random variables:
   \begin{itemize}
   \item [SRVar(V)]: for sampled shared variable $V$
   \item [ORVar(R,i)]: for variable $R_i$ sampled in $i$-th oracle query
   \end{itemize}}
*)
type rvar =
  | SRVar of II.id
  | ORVar of II.id * query_idx

(*i*)
let string_of_rvar r = match r with
  | SRVar i      -> i
  | ORVar (i, q) -> F.sprintf "%s_%i" i q

let pp_rvar fmt r = pp_string fmt (string_of_rvar r)
(*i*)

(* \ic{Parameters:
   \begin{itemize}
   \item [FOParam(m,i)] $= m_i$: oracle parameter $m \in \field$ of $i$-th query
   \item [OCoeff(M,i,j)]$= \alpha^{M}_{i,j}$: for the oracle argument $M \in \group_n$
      in the $i$-query, this is the coefficient of the $j$-th element in
      the completion for $\group_n$ before the oracle call.
   \item [FChoice(m')] $=m'$: value $m' \in \field$ chosen by adversary for winning condition.
   \item [ChoiceCoeff(M')]$=\beta^{M'}_j$: for the value $M' \in \group_n$ chosen by the
      adversary for the winning condition, this is the coefficient of $j$-th element
      in the completion for $\group_n$ after the last oracle call.
   \end{itemize}}
*)
type param =
  | FOParam of II.id * query_idx
  | OCoeff  of II.id * query_idx * coeff_idx
  | FChoice of II.id
  | ChoiceCoeff of II.id * coeff_idx

(*i*)
let string_of_param p = match p with
  | FOParam (id, q)     -> F.sprintf "%s_%i" id q
  | OCoeff  (id, q, i)  -> F.sprintf "%s_%i_%i" id q i
  | FChoice id          -> id
  | ChoiceCoeff (id, i) -> F.sprintf "%s_%i" id i

let pp_param fmt p = pp_string fmt (string_of_param p)
(*i*)

(* \ic{A variable is either a random variable or a parameter.} *)
type var =
  | RVar  of rvar
  | Param of param

(*i*)
let pp_var fmt v = match v with
  | RVar r  -> pp_rvar fmt r
  | Param p -> pp_param fmt p
(*i*)

(* \ic{Define polynomials $\ZZ[params,rvars]$ used to compute constraints.} *)
module GP = MakePoly(struct
  type t      = var
  let pp      = pp_var
  let equal   = (=)
  let compare = compare
end) (IntRing)

type gpoly = GP.t

(*i ********************************************************************* i*)
(* \hd{Symbolic completion} *)
(*i ********************************************************************* i*)

(* \ic{State of the completion computation:
   \begin{itemize}
   \item [known]: Basis for known values in each group.
   \item [hmap]: During oracle queries, handles get replaced by
     linear combinations of known values. We store these for making
     the winning condition handle-free.
   \end{itemize}}
*)
type state = {
  known : (II.gid * gpoly) list;
  hmap  : ((II.id * II.gid * query_idx) * gpoly) list
}

(* \ic{Return polys for [gid] in list.}*)
let polys_for_gid gid known =
  L.filter ((=) gid << fst) known
  |> L.map snd

(* \ic{Extract separate lists for each [gid] from common list.} *)
let poly_gid_lists known =
  let gids = L.map fst known |> sorted_nub compare in
  let list_for_gid gid =
    match L.filter ((=) gid << fst) known with
    | []                  -> None
    | ((gid,_)::_) as gps -> Some (gid,L.map snd gps)
  in
  catSome (L.map list_for_gid gids)

(*i*)
let pp_state fmt st =
  F.fprintf fmt "---------- Group elements ----------\n";
  L.iter
    (fun (gid, ps) -> F.fprintf fmt "\nGroup G%s:\n%a\n" gid (pp_list "\n" GP.pp) ps)
    (poly_gid_lists st.known);
  F.fprintf fmt "\n------- Handle substitutions -------\n";
  L.iter (fun ((id, gid, q), p) -> F.fprintf fmt "\n%s_%i in G%s = %a\n" id q gid GP.pp p) st.hmap
(*i*)

(* \ic{Create linear combination of polynomials [ps]
   such that the $j$-polynomial is multiplied by
   coefficient polynomial [cgen j].}*)
let lin_comb_of_gps ps cgen =
  GP.(ladd (mapi' (fun i p -> cgen i *@ p) ps))

(* \ic{Convert oracle polynomial to [gp] for given state [st] and query index [i].} *)
let op_to_gp st i p =
  let vconv v = match v with
    | II.Param(tid) ->
      begin match tid.II.tid_ty with
      | II.Field ->
        GP.var (Param (FOParam(tid.II.tid_id,i)))
      | II.Group gid ->
        L.assoc (tid.II.tid_id,gid,i) st.hmap
      end
    | II.SRVar(id) ->
      GP.var (RVar (SRVar(id)))
    | II.ORVar(id) ->
      GP.var (RVar (ORVar(id,i)))
  in
  OP.to_terms p |> GP.eval_generic GP.const vconv


(* \ic{Complete state [st] with return values from
   call to [od] which is the [i]-th oracle call.} *)
let complete_oracle od i st =

  (* \ic{We first extend the handle map.} *)
  let entry_of_handle (hid,gid) =
    let p =
      lin_comb_of_gps
        (polys_for_gid gid st.known)
        (fun j -> GP.var (Param (OCoeff(hid,i,j))))
     in
     ((hid,gid,i), p)
  in
  let get_handle v =
    match v with
    | II.Param tid ->
      begin match tid.II.tid_ty with
      | II.Group gid -> Some (tid.II.tid_id, gid)
      | II.Field     -> None
      end
    | _ -> None
  in
  let handles =
    conc_map OP.vars (L.map fst od.II.odef_return)
    |> L.map get_handle
    |> catSome
    |> sorted_nub compare
  in
  let hmap_new = L.map entry_of_handle handles in
  let st = { st with hmap  = st.hmap @ hmap_new } in

  (* \ic{Add oracle return values to known values.} *)
  let known_new =
    L.map (fun (p,gid) -> (gid,op_to_gp st i p)) od.II.odef_return
  in
  { st with known = st.known @ known_new }

(* \ic{Complete state [st] with respect to group-setting [gs].}*)
let complete_gs _gs st = st

(* \ic{Complete state [st] with respect to given group setting [gs]
   and sequence of oracles calls [ocalls].} *)
let rec complete_st gs ocalls st =
  let st = complete_gs gs st in
  match ocalls with
  | [] ->
    st
  | (i,od)::ocalls ->
    let st = complete_oracle od i st in
    complete_st gs ocalls st

(*i ********************************************************************* i*)
(* \hd{Parameter coefficient extraction} *)
(*i ********************************************************************* i*)

(* \ic{Define polynomials $\ZZ[params]$.} *)
module CP = MakePoly(struct
  type t      = param
  let pp      = pp_param
  let equal   = (=)
  let compare = compare
end) (IntRing)

(* \ic{These polynomials constitute a ring.} *)
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

(* \ic{Define polynomial $(\ZZ[params])[rvars]$.} *)
module EP = MakePoly(struct
  type t      = rvar
  let pp      = pp_rvar
  let equal   = (=)
  let compare = compare
end) (CPR)

(* \ic{Convert [gp] to [ep].} *)
let gp_to_ep =
  let vconv v = match v with
    | RVar r  -> EP.var r
    | Param p -> EP.const (CP.var p)
  in
  EP.eval_generic (EP.const << CP.const) vconv << GP.to_terms

(* \ic{Extract coefficients, these are the constraints.} *)
let extract_constraints = L.map snd << EP.to_terms << gp_to_ep

(* \ic{Convert [cp] to [rpoly].} *)
let cp_to_rpoly =
  RP.eval_generic RP.const (RP.var << string_of_param) << CP.to_terms

(*i ********************************************************************* i*)
(* \hd{Translation from winning conditions to constraints} *)
(*i ********************************************************************* i*)

(* \ic{Create coefficient for handle [hid] and index i.} *)
let pgen_gchoice hid i = GP.var (Param (ChoiceCoeff (hid, i)))

(* \ic{Convert (non-quantified) winning condition polynomial
   to list of [gp].} *)
let nonquant_wp_to_gp st p =
  let vconv v = match v with
    | II.RVar id ->
      GP.var (RVar (SRVar id))
    | II.OParam _ ->
      failwith "nonquant_wp_to_qp: oracle parameter not allowed"
    | II.Choice tid ->
      begin match tid.II.tid_ty with
      | II.Field ->
        GP.var (Param (FChoice(tid.II.tid_id)))
      | II.Group gid ->
        lin_comb_of_gps (polys_for_gid gid st.known) (pgen_gchoice tid.II.tid_id)
      end
  in
  WP.to_terms p |> GP.eval_generic GP.const vconv

(* \ic{Convert (implicitly) quantified winning condition polynomial
   to list of [gp]s.} *)
let quant_wp_to_gps st bound p =
  let ps = L.map (fun qidx -> (qidx,p)) (list_from_to 1 bound) in
  let vconv qidx v = match v with
    | II.RVar id ->
      GP.var (RVar (SRVar id))
    | II.OParam tid ->
      begin match tid.II.tid_ty with
      | II.Field ->
        GP.var (Param (FOParam (tid.II.tid_id, qidx)))
      | II.Group gid ->
        L.assoc (tid.II.tid_id, gid, qidx) st.hmap
      end
    | II.Choice tid ->
      begin match tid.II.tid_ty with
      | II.Field ->
        GP.var (Param (FChoice(tid.II.tid_id)))
      | II.Group gid ->
        lin_comb_of_gps (polys_for_gid gid st.known) (pgen_gchoice tid.II.tid_id)
      end
  in
  L.map (fun (qidx,p) -> WP.to_terms p |> GP.eval_generic GP.const (vconv qidx)) ps

(* \ic{Returns [true] if winning polynomials is implicitly quantified,
   i.e., it contains an oracle parameters} *)
let is_quantified f =
  let is_qvar v = match v with II.OParam _ -> true | _ -> false in
  L.exists is_qvar (WP.vars f)

(* \ic{Convert game definition to initial state. Ensure that every
   input list contains $1$ exactly once.} *)
let gdef_to_state gdef =
  let rpoly_to_gp =
    GP.eval_generic GP.const (fun v -> GP.var (RVar (SRVar v))) << RP.to_terms
  in
  let inputs_for gid =
       L.filter ((=) gid << snd) gdef.II.gdef_inputs
    |> L.map (rpoly_to_gp << fst)
    |> sorted_nub compare
    |> (fun gps -> (GP.from_int 1)::gps)
    |> L.map (fun gp -> (gid,gp))
  in
  { known = conc_map inputs_for (II.gids_in_gdef gdef);
    hmap = [] }

(* \ic{Convert game definition to equality and inequality constraints.} *)
let gdef_to_constrs b gdef =
  let p_header h s = F.printf ("\n############ %s ###########\n%s") h s in
  let st = gdef_to_state gdef in
  let ocalls =
    match gdef.II.gdef_odefs with
    | [od] -> mapi' pair (replicate od b)
    | []   -> []
    | _    -> failwith "gdef_to_constrs: impossible, more than one oracle"
  in
  let st = complete_st gdef.II.gdef_gs ocalls  st in

  F.printf "%a" pp_state st;

  let eqs = gdef.II.gdef_wcond.II.wcond_eqs in
  let ineqs = gdef.II.gdef_wcond.II.wcond_ineqs in
  let (qeqs, eqs) = L.partition is_quantified eqs in
  let (qineqs, ineqs) = L.partition is_quantified ineqs in

  p_header "Equalities" (fsprintf "%a\n" (pp_list "\n" WP.pp) eqs);
  p_header "Quantified Equalities" (fsprintf "%a\n" (pp_list "\n" WP.pp) qeqs);
  p_header "Inequalities" (fsprintf "%a\n" (pp_list "\n" WP.pp) ineqs);
  p_header "Quantified Inequalities" (fsprintf "%a\n" (pp_list "\n" WP.pp) qineqs);

  if qeqs <> [] then failwith "Only inequalities can contain oracle parameters.";

  let qineqs = conc_map (quant_wp_to_gps st b) qineqs in
  p_header "Unrolled Inequalities" (fsprintf "%a\n" (pp_list "\n" GP.pp) qineqs);

  let eqs = L.map (nonquant_wp_to_gp st) eqs in
  let ineqs = L.map (nonquant_wp_to_gp st) ineqs in

  p_header
    "Equalities for constraint generation"
    (fsprintf "0 = %a\n" (pp_list "\n\n0 = " EP.pp) (L.map gp_to_ep eqs));

  p_header
    "Inequalities for constraint generation"
    (fsprintf "0 <> %a\n" (pp_list "\n\n0 <> " EP.pp) (L.map gp_to_ep ineqs));

  let eqs_constrs = conc_map extract_constraints eqs in

  p_header
    "Equality constraints"
    (fsprintf "0 = %a\n" (pp_list "\n\n0 = " RP.pp) (L.map cp_to_rpoly eqs_constrs));

  let ineqs_constrs = L.map extract_constraints (ineqs @ qineqs) in

  p_header "Inequality constraints" "";
  L.iter
    (fun fs ->
       F.printf "%a\n" (pp_list " \\/ " (fun fmt f -> F.fprintf fmt "%a <> 0" RP.pp f)) fs)
    (L.map (fun f -> L.map cp_to_rpoly f) ineqs_constrs);
  
  (L.map cp_to_rpoly eqs_constrs, L.map (fun f -> L.map cp_to_rpoly f) ineqs_constrs)