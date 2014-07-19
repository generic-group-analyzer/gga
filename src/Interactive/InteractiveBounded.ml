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
  known : (II.gid * gpoly list) list;
  hmap : ((II.id * II.gid * query_idx) * gpoly) list
}

(*i*)
let pp_state fmt st =
  F.fprintf fmt "---------- Group elements ----------\n";
  L.iter (fun (gid, ps) -> F.fprintf fmt "\nGroup G%s:\n%a\n" gid (pp_list "\n" GP.pp) ps) st.known;
  F.fprintf fmt "\n------- Handle substitutions -------\n";
  L.iter (fun ((id, gid, q), p) -> F.fprintf fmt "\n%s_%i in G%s = %a\n" id q gid GP.pp p) st.hmap
(*i*)

let state_update_hmaps keyvals st =
  {st with hmap = keyvals @ st.hmap}

(*i This adds a polynomial to the list for gid.
   Note: We add the updated group list to the front of the list, since
         assoc always returns the first most up-to-date list. Maybe replace
         by better data structure in the future...??

         The pretty printer needs to be fixed, since it prints the whole
         list. Alternatively replace with a Map. i*)
let state_app_group gid p st =
  try
    let l =  L.assoc gid st.known in
    {st with known = (gid, p :: l) :: st.known}
  with
    | Not_found ->
      (*i If the first element added is "1", don't add it twice i*)
      if GP.is_const p
      then {st with known = (gid, [p]) :: st.known}
      else {st with known = (gid, p :: [GP.from_int 1]) :: st.known}


let lin_comb_of_gps ps pgen  =
  GP.(ladd (mapi' (fun i p -> pgen i *@ p) ps))

(*i This function does the following:
   1. Replaces all handles in given poly with a linear combination of computable monomials.
   2. Adds the polynomial into the group it belongs to.
   3. For each new handle record its value in the state. 
i*)
let add_poly groups st gid p q =
  (*i Keep track of handle values defined to be added to state i*)
  let hmap = ref [] in
  let set_map id v = hmap := ((id, gid, q), v) :: !hmap in
  let get_handle_value hid =
    (*i First check if already stored in our old state i*)
    try L.assoc (hid, gid, q) st.hmap with
    | Not_found ->
    try L.assoc (hid, gid, q) !hmap with
    | Not_found -> begin
                   let pgen i = GP.var (Param (OCoeff (hid, q, i))) in
                   let v = lin_comb_of_gps (try L.assoc gid groups with | _ -> [GP.from_int 1]) pgen in
                   set_map hid v; v
                   end
  in
  (*i Convert ovars to GP polynomials and update hmap on each converted handle i*)
  let ovar_to_gp v =
    match v with
    | II.SRVar r -> GP.var (RVar (SRVar r))
    | II.ORVar r -> GP.var (RVar (ORVar (r, q)))
    | II.Param t -> if t.II.tid_ty = II.Field
                  then GP.var (Param (FOParam (t.II.tid_id, q)))
                  else get_handle_value t.II.tid_id
  in
  (*i Adds polynomial to the group gid and adds handle value mappings i*)
  let update_state p =
    let st = state_app_group gid p st in
    state_update_hmaps !hmap st
  in
  OP.to_terms p
  |> GP.eval_generic GP.const ovar_to_gp
  |> update_state


let call_oracle o q st =
  let rec loop st' rvals =
    match rvals with
    | (p, gid) :: xs -> loop (add_poly st.known st' gid p q) xs
    | []             -> st'
  in
  loop st o.II.odef_return

(*i TODO: Add completion computation with respect to group setting i*)
let complete_gs _gs st =
  st

let compute_completion st o bound gs =
  let rec loop q st =
    if q > bound then st
    else complete_gs gs st
         |> call_oracle o q
         |> complete_gs gs
         |> loop (q+1)
  in
  loop 1 st

(*i ********************************************************************* i*)
(* \hd{Parameter coefficient extraction} *)
(*i ********************************************************************* i*)

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

let gp_to_ep =
  let vconv v = match v with
    | RVar r  -> EP.var r
    | Param p -> EP.const (CP.var p)
  in
  EP.eval_generic (EP.const << CP.const) vconv << GP.to_terms

let extract_constraints = L.map snd << EP.to_terms << gp_to_ep

let cp_to_rpoly =
  RP.eval_generic RP.const (RP.var << string_of_param) << CP.to_terms

(*i ********************************************************************* i*)
(* \hd{Translation from winning condition to constraints} *)
(*i ********************************************************************* i*)

let rpoly_to_gp p =
  let cconv i = GP.const i in
  let vconv v = GP.var (RVar (SRVar v)) in
  RP.to_terms p |> GP.eval_generic cconv vconv

let get_gid tid = match tid.II.tid_ty with | II.Group s -> s | _ -> failwith "Uhh?"

let pgen hid i = GP.var (Param (ChoiceCoeff (hid, i)))

let nonquant_wp_to_gp st p =
  let cconv c = GP.const c in
  let vconv v = match v with
    | II.RVar id ->
      GP.var (RVar (SRVar id))
    | II.OParam _ ->
      failwith "nonquant_wp_to_qp: oracle parameter not allowed"
    | II.Choice tid when II.is_field_tid tid ->
      GP.var (Param (FChoice(tid.II.tid_id)))
    | II.Choice tid ->
      let ps = L.assoc (get_gid tid) st.known in
      lin_comb_of_gps ps (pgen tid.II.tid_id)
  in
  WP.to_terms p |> GP.eval_generic cconv vconv

let quant_wp_to_gps st bound p =
  let ps = L.map (fun qidx -> (qidx,p)) (list_from_to 1 bound) in
  let cconv c = GP.const c in
  let vconv qidx v = match v with
    | II.RVar id ->
      GP.var (RVar (SRVar id))
    | II.OParam tid when II.is_field_tid tid ->
      GP.var (Param (FOParam (tid.II.tid_id, qidx)))
    | II.OParam tid ->
      L.assoc (tid.II.tid_id, get_gid tid, qidx) st.hmap
    | II.Choice tid when II.is_field_tid tid ->
      GP.var (Param (FChoice(tid.II.tid_id)))
    | II.Choice tid ->
      let ps = L.assoc (get_gid tid) st.known in
      lin_comb_of_gps ps (pgen tid.II.tid_id)
  in
  L.map (fun (qidx,p) -> WP.to_terms p |> GP.eval_generic cconv (vconv qidx)) ps

(* \ic{Returns [true] if winning polynomials is implicitly quantified,
   i.e., it contains an oracle parameters} *)
let is_quantified f =
  let is_qvar v = match v with II.OParam _ -> true | _ -> false in
  L.exists is_qvar (WP.vars f)

let gdef_to_state gdef =
  L.fold_left (fun acc (p, gid) -> state_app_group gid (rpoly_to_gp p) acc)
              { known = []; hmap = [] }
              gdef.II.gdef_inputs
  
let gdef_to_constrs b gdef =
  let st = gdef_to_state gdef in
  let st = compute_completion st (L.hd gdef.II.gdef_odefs) b gdef.II.gdef_gs in

  F.printf "%a" pp_state st;

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

  F.printf "\n############ Unrolled Inequalities ###########\n";
  let qineqs = conc_map (quant_wp_to_gps st b) qineqs in
  F.printf "%a\n" (pp_list "\n" GP.pp) qineqs;

  let eqs = L.map (nonquant_wp_to_gp st) eqs in
  let ineqs = L.map (nonquant_wp_to_gp st) ineqs in

  F.printf "\n############ Equalities for constraint generation ###########\n";
  F.printf "0 = %a\n" (pp_list "\n\n0 = " EP.pp) (L.map gp_to_ep eqs);

  F.printf "\n############ Inequalities for constraint generation ###########\n";
  F.printf "0 <> %a\n" (pp_list "\n\n0 <> " EP.pp) (L.map gp_to_ep ineqs);

  let eqs_constrs = conc_map extract_constraints eqs in

  F.printf "\n############## Equality constraints ##############\n";
  F.printf "0 = %a\n" (pp_list "\n\n0 = " RP.pp) (L.map cp_to_rpoly eqs_constrs);

  let ineqs_constrs = L.map extract_constraints (ineqs @ qineqs) in

  F.printf "\n############## Inequality constraints ##############\n";
  L.iter (fun fs ->
         F.printf "%a\n" (pp_list " \\/ " (fun fmt f -> F.fprintf fmt "%a <> 0" RP.pp f)) fs)
         (L.map (fun f -> L.map cp_to_rpoly f) ineqs_constrs);
  
  (L.map cp_to_rpoly eqs_constrs, L.map (fun f -> L.map cp_to_rpoly f) ineqs_constrs)