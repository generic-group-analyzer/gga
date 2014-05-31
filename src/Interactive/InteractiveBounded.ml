(*s Bounded analysis for interactive assumptions. *)

(*i*)
(* open Util *)
open Util
open Poly

module IR = IntRing
module II = InteractiveInput
module S = String
module RP = II.RP
module WP = II.WP
module OP = II.OP
(*i*)

(* \hd{Parameter polynomials.} *)

type idx = int

type input_idx = int

type oreturn_idx = int

type oparam_id = II.oparam_id * II.oname

type param =
  | OParam      of oparam_id * idx
  | FieldChoice of II.fchoice_id
  | ICoeff      of II.gchoice_id * input_idx
  | OCoeff      of II.gchoice_id * II.oname * oreturn_idx * idx

(*i*)
let pp_param fmt p =
  match p with
  | OParam((m,_o),i)  -> F.fprintf fmt "%s_%i" m i
  | FieldChoice(w)    -> F.fprintf fmt "%s" w
  | ICoeff(u,j)       -> F.fprintf fmt "%s_I_%i" u j
  | OCoeff(u,_o,j,i)  -> F.fprintf fmt "%s_O_%i_%i" u j i
(*i*)

module PP = MakePoly(struct
  type t = param
  let pp = pp_param
  let equal = (=)
  let compare = compare
end) (IntRing)

module PPolyRing = struct
  type t = PP.t
  let pp = PP.pp

  let add  = PP.add
  let opp  = PP.opp
  let mult = PP.mult
  let one  = PP.one
  let zero : PP.t = PP.zero
  let ladd cs = L.fold_left (fun acc c -> PP.add c acc) PP.zero cs
  let from_int i = PP.const (Big_int.big_int_of_int i)
  let equal = PP.equal
  let compare = PP.compare
  let use_parens = true
end

(* \hd{Polynomials with (indexed) random variables
       and parameter polynomial coefficients} *)

type orvar_id = II.orvar_id * II.oname

type var =
  | SRVar of II.rvar_id
  | ORVar of orvar_id * idx

let pp_var fmt v =
  match v with
  | SRVar(x)        -> F.fprintf fmt "%s" x
  | ORVar((a,_o),i) -> F.fprintf fmt "%s_%i" a i

module RPP = MakePoly(struct
  type t = var
  let pp = pp_var
  let equal = (=)
  let compare = compare
end) (PPolyRing)

(* \hd{Conversions between polynomials} *)

let ovar_to_rpp i o v =
  match v with
  | II.Param(v) -> RPP.const (PP.var (OParam((v,o),i)))
  | II.SRVar(v) -> RPP.var (SRVar(v))
  | II.ORVar(v) -> RPP.var (ORVar((v,o),i))

let opoly_term_to_rpp i o (vs,c) =
  RPP.mult (RPP.const (PP.const c)) (RPP.lmult (L.map (ovar_to_rpp i o) vs))

let opoly_to_rpp i o op =
  RPP.ladd (L.map (opoly_term_to_rpp i o) (OP.to_terms op))

let rpoly_term_to_rpp (vs,c) =
  RPP.mult
    (RPP.const (PP.const c))
    (RPP.lmult (L.map (fun v -> (RPP.var (SRVar(v)))) vs))

let rpoly_to_rpp rp = RPP.ladd (L.map rpoly_term_to_rpp (RP.to_terms rp))

let wvar_to_rpp i gchoices v =
  match v with
  | II.OParam(v)      -> RPP.const (PP.var (OParam((v,"on"),i)))
  | II.RVar(v)        -> RPP.var (SRVar(v))
  | II.GroupChoice(v) -> L.assoc v gchoices
  | II.FieldChoice(v) -> RPP.const (PP.var (FieldChoice(v)))

let wpoly_term_to_rpp i gchoices (vs,c) =
  RPP.mult
    (RPP.const (PP.const c))
    (RPP.lmult (L.map (wvar_to_rpp i gchoices) vs))

let wcond_to_rpp i gchoices wp =
  RPP.ladd (L.map (wpoly_term_to_rpp i gchoices) (WP.to_terms wp))


let param_to_string p =
  match p with
  | OParam((m,_o),i)  -> F.sprintf "%s_%i" m i
  | FieldChoice(w)    -> F.sprintf "%s" w
  | ICoeff(u,j)       -> F.sprintf "%s_I_%i" u j
  | OCoeff(u,_o,j,i)  -> F.sprintf "%s_O_%i_%i" u j i

let ppoly_term_to_rp (vs,c) =
  RP.mult
    (RP.const c)
    (RP.lmult (L.map (fun v -> param_to_string v |> RP.var) vs))

let ppoly_to_rp pp =
  RP.ladd (L.map ppoly_term_to_rp (PP.to_terms pp))

(* \hd{Linear combinations of polynomials represent returned group elements} *)

let rpp_of_gdef b gdef gchoice =
  let inputs = gdef.II.gdef_inputs in
  let odefs = gdef.II.gdef_odefs in

  (* \ic{Linear combination of adversary inputs.} *)
  let f1 =
    zip_indices inputs
    |> L.map (fun (n,rp) -> RPP.mult (RPP.const (PP.var (ICoeff(gchoice,n)))) (rpoly_to_rpp rp))
    |> RPP.ladd
  in

  (* \ic{Linear combination of oracle return values.} *)  
  let rpp_of_opoly i n o op =
    RPP.mult
      (RPP.const (PP.var (OCoeff(gchoice,o,n,i))))
      (opoly_to_rpp i o op)
  in
  let rpp_of_odef i (o,ops) =
    zip_indices ops
    |> L.map (fun (n,op) -> rpp_of_opoly i n o op)
    |> RPP.ladd
  in
  let os i = RPP.ladd (L.map (rpp_of_odef i) odefs) in
  RPP.add f1 (RPP.ladd (L.map os (list_from_to 1 b)))

(* \hd{Translate game definition into polynomial constraints for a given bound} *)

let gdef_to_constrs b gdef =
  let gchoices =
    L.map (fun v -> (v, rpp_of_gdef b gdef v)) (II.gchoices_of_gdef gdef)
  in
  F.printf "#########################################################\n";
  F.printf "Group elements returned by adversary:\n\n";

  List.iter (fun (v,f) -> F.printf "%s = %a\n" v RPP.pp f) gchoices;

  let eqs = gdef.II.gdef_wcond.II.wcond_eqs in
  let ineqs = gdef.II.gdef_wcond.II.wcond_ineqs in

  let is_oparam = function II.OParam(_) -> true | _ -> false in

  let qeqs, eqs = L.partition (fun wp -> L.exists is_oparam (WP.vars wp)) eqs in

  let qineqs, ineqs = L.partition (fun wp -> L.exists is_oparam (WP.vars wp)) ineqs in

  if qeqs <> [] then
    failwith "only inequality constraints allowed to contain oracle parameter";

  let eqs_rpps = L.map (wcond_to_rpp 1 gchoices) eqs in

  let ineqs_rpps = L.map (wcond_to_rpp 1 gchoices) ineqs in

  let ineqs_rpps =
      ineqs_rpps
    @ conc_map (fun i -> L.map (wcond_to_rpp i gchoices) qineqs) (list_from_to 1 b)
  in

  F.printf "\n#########################################################\n";
  F.printf "Winning condition polynomials:\n\n";

  List.iter (fun f -> F.printf "@[0 =@.  %a@]\n" RPP.pp_break f) eqs_rpps;

  List.iter (fun f -> F.printf "@[0 <>@.  %a@]\n" RPP.pp_break f) ineqs_rpps;

  F.printf "\n#########################################################\n";
  F.printf "Winning condition constraints:\n";

  let get_coeffs rpp = L.map (fun m -> RPP.coeff rpp m) (RPP.mons rpp) in

  let simp_constr pp =
    if L.for_all (fun (_,c) -> IntRing.compare c IntRing.zero < 0) (PP.to_terms pp)
    then PP.mult (PP.const (IntRing.opp IntRing.one)) pp
    else pp
  in

  let zero_constrs  =
    conc_map get_coeffs eqs_rpps |> L.map (fun f -> simp_constr f |> ppoly_to_rp)
  in
  let nzero_constrs =
    L.map get_coeffs ineqs_rpps |> L.map (L.map (fun f -> simp_constr f |> ppoly_to_rp))
  in

  List.iter (fun f -> F.printf "@[0 = %a@]@." RP.pp f) zero_constrs;
  List.iter
    (fun fs ->
       F.printf "%a\n" (pp_list " \\/ " (fun fmt f -> F.fprintf fmt "%a <> 0" RP.pp f)) fs)
    nzero_constrs;

  (zero_constrs, nzero_constrs)