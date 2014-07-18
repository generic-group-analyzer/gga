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

(* State of the completion computation:
   - groups: Contains a monomial basis for each group

   - handle_values: During oracle queries, handles get replaced by
     linear combinations. We store these for constraint generation
*)

type state = {
  groups : (II.gid * GP.t list) list;
  hmap : ((II.id * II.gid * query_idx) * GP.t) list
}

let pp_state fmt st =
  F.fprintf fmt "---------- Group elements ----------\n";
  L.iter (fun (gid, ps) -> F.fprintf fmt "\nGroup G%s:\n%a\n" gid (pp_list "\n" GP.pp) ps) st.groups;
  F.fprintf fmt "\n------- Handle substitutions -------\n";
  L.iter (fun ((id, gid, q), p) -> F.fprintf fmt "\n%s_%i in G%s = %a\n" id q gid GP.pp p) st.hmap

let state_update_hmaps keyvals st =
  {st with hmap = keyvals @ st.hmap}

(* This adds a polynomial to the list for gid.
   Note: We add the updated group list to the front of the list, since
         assoc always returns the first most up-to-date list. Maybe replace
         by better data structure in the future...??

         The pretty printer needs to be fixed, since it prints the whole
         list. Alternatively replace with a Map. *)

let state_app_group gid p st =
  try let l =  L.assoc gid st.groups
      in
      {st with groups = (gid, p :: l) :: st.groups}
  with
  | _ ->
  (* If the first element added is "1", don't add it twice *)
  if GP.is_const p
  then {st with groups = (gid, [p]) :: st.groups}
  else {st with groups = (gid, p :: [GP.from_int 1]) :: st.groups}

let lin_comb_of_gps ps cgen =
  L.fold_left (fun acc p -> GP.add acc (GP.mult (cgen ()) p))
              GP.zero
              ps

let make_fresh_var_gen s q =
  let i = ref 0 in
  function () -> i := !i+1;
                 GP.var (Param (OCoeff (s, q, !i)))


(* This function does the following:
   1. Replaces all handles in given poly with a linear combination of computable monomials.
   2. Adds the polynomial into the group it belongs to.
   3. For each new handle record its value in the state. 
   *)
let add_poly groups st gid p q =
  (* Keep track of handle values defined to be added to state *)
  let hmap = ref []
  in
  let set_map id v = hmap := ((id, gid, q), v) :: !hmap
  in  
  let get_handle_value id =
    (* First check if already stored in our old state *)
    try L.assoc (id, gid, q) st.hmap with
    | Not_found ->
    try L.assoc (id, gid, q) !hmap with
    | Not_found -> begin
                   let v = lin_comb_of_gps (try L.assoc gid groups with | _ -> [GP.from_int 1])
                              (make_fresh_var_gen (F.sprintf "C_%s" id) q)
                   in set_map id v; v
                   end
  in
  (* Convert ovars to GP polynomials and update hmap on each converted handle *)
  let ovar_to_gp v =
    match v with
    | II.SRVar r -> GP.var (RVar (SRVar r))
    | II.ORVar r -> GP.var (RVar (ORVar (r, q)))
    | II.Param t -> if t.II.tid_ty = II.Field
                  then GP.var (Param (FOParam (t.II.tid_id, q)))
                  else get_handle_value t.II.tid_id
  in
  (* Adds polynomial to the group gid and adds handle value mappings *)
  let update_state p =
    let st = state_app_group gid p st in
    state_update_hmaps !hmap st
  in
  OP.to_terms p
  |> GP.eval_generic (fun i -> GP.const i) ovar_to_gp
  |> update_state


let call_oracle o q st =
  let rec loop st' rvals =
    match rvals with
    | (p, gid) :: xs -> loop (add_poly st.groups st' gid p q) xs
    | []             -> st'
  in
  loop st o.II.odef_return

(* TODO: Add completion computation with respect to group setting *)
let complete_gs gs st =
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

let get_gid tid = match tid.II.tid_ty with | Group s -> s | _ -> failwith "Uhh?"

let nonquant_wp_to_gp st p =
  let cconv c = GP.const c in
  let vconv v = match v with
    | II.RVar id    -> GP.var (RVar (SRVar id))
    | II.OParam _   -> failwith "Called with quantified winning condition."
    | II.Choice tid -> if tid.II.tid_ty = II.Field
                       then GP.var (Param (FChoice(tid.II.tid_id)))
                       else begin
                              let gid = get_gid tid in
                              let ps = L.assoc gid st.groups in
                              lin_comb_of_gps ps (cgen (F.sprintf "C_%s" tid.II.tid_id))
                            end
  in
  WP.to_terms p |> GP.eval_generic cconv vconv

let quant_wp_to_gps st bound p =
  let ps = L.map (fun _ -> p) (list_from_to 1 bound) in
  let q = ref 0 in
  let cconv c = GP.const c in
  let vconv v = match v with
    | II.RVar id    -> GP.var (RVar (SRVar id))
    | II.OParam tid -> if tid.II.tid_ty = II.Field
                       then GP.var (Param (FOParam (tid.II.tid_id, !q)))
                       else begin
                              let gid = get_gid tid in
                              L.assoc (tid.II.tid_id, gid, !q) st.hmap
                            end
    | II.Choice tid -> if tid.II.tid_ty = II.Field
                       then GP.var (Param (FChoice(tid.II.tid_id)))
                       else begin
                              let gid = get_gid tid in
                              let ps = L.assoc gid st.groups in
                              lin_comb_of_gps ps (cgen (F.sprintf "C_%s" tid.II.tid_id))
                            end
  in  
  L.map (fun p -> q := !q + 1; WP.to_terms p |> GP.eval_generic cconv vconv) ps

(* Checks if a wpoly is quantified, i.e. contains oracle parameters *)
let is_quantified f =
  let is_qvar v = match v with | II.OParam _ -> true | _ -> false in
  L.fold_left (fun acc v -> acc || is_qvar v) false (WP.vars f)

let gdef_to_state gdef =
  L.fold_left (fun acc (p, gid) -> state_app_group gid (rpoly_to_gp p) acc)
              { groups = []; hmap = [] }
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