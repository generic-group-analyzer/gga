(* This file is distributed under the MIT License (see LICENSE). *)

(*s Interpret commands for defining interactive problems. *)

(*i*)
open InteractiveInput
open Util
open LPoly

module F = Format
(*i*)

(*******************************************************************)
(* \hd{Commands to define games} *)

(* \ic{For winning condition input, we use polynomials in $\ZZ[\vec{X}]$
       for variables $\vec{X}$ that are either indexed or not.} *)

(* \ic{Variables in winning condition input are either non-indexed or indexed.} *)
type ivar = 
  | NIVar of id
  | IVar  of id

(*i*)
let string_of_ivar v = match v with
  | IVar s  -> s^"_i"
  | NIVar s -> s

let pp_ivar fmt v = pp_string fmt (string_of_ivar v)
(*i*)

module IP = MakePoly(struct
  type t = ivar
  let pp = pp_ivar
  let equal = (=)
  let compare = compare
end) (IntRing)

type ipoly = IP.t

type cond_type = Eq | InEq

(* \ic{We use [rpoly]s for all types of commands and convert later on when
       we have all information required to distinguish the different types
       of variables.
       \begin{itemize}
       \item [AddSampling(ids)]: add global sampling of random variables.
       \item [AddIsos(isos)]: add isomorphisms to group setting.
       \item [AddMaps(isos)]: add maps to group setting.
       \item [AddInput(f)]: Add $f$ to adversary inputs.
       \item [AddOracle(on, tids, ids, rps)]: Add the oracle where the name
           is denoted by $on$,, the (typed) arguments are denoted by $tids$,
           the sampled random values are denoted by $ids$, and
           the returned polynomials together with the group identifier are
           denoted by $rps$.
       \item [SetWinning(tids, wps)]:
         Set the winning condition where winning condition polynomials
         together with ineq or eq are denoted by $wps$ and (typed) values chosen by
         the adversary are denoted by $tids$.
       \end{itemize}
      Note that even though we use [ipoly] for AddInput, AddOracle, and SetWinning,
      indexed variables are only allowed in SetWinning.} *)
type cmd =
  | AddSamplings of id list
  | AddIsos      of iso list
  | AddMaps      of emap list
  | AddInput     of ipoly list * gid
  | AddOracle    of oname * tid list * id list * (ipoly * gid) list
  | SetWinning   of tid list * (ipoly * cond_type) list

(*i*)
let pp_cmd fmt cmd =
  let cty_to_string = function Eq -> " = 0" | InEq -> " <> 0" in
  match cmd with
  | AddSamplings ids ->
    F.fprintf fmt "add samplings: %a.\n" (pp_list ", " pp_string) ids
  | AddIsos isos ->
    F.fprintf fmt "isos: %a.\n" (pp_list ", " pp_iso) isos
  | AddMaps emaps ->
    F.fprintf fmt "maps: %a.\n" (pp_list ", " pp_emap) emaps
  | AddInput (fs,gid) ->
    F.fprintf fmt "add_input %a in %s\n" (pp_list "," IP.pp) fs gid
  | AddOracle(s,params,orvars,fs) ->
    F.fprintf fmt "add_oracle %s(%a) sample %a; (%a)" s
      (pp_list ", " pp_tid) params
      (pp_list ", " pp_string) orvars
      (pp_list ", "
         (fun fmt (rp,gid) -> F.fprintf fmt "%a in %a" IP.pp rp pp_ty (Group gid))) fs
  | SetWinning(choices,conds) ->
    F.fprintf fmt "set_winning (%a) cond: %a"
      (pp_list ", " pp_tid) choices
      (pp_list " /\\ "
         (fun fmt (f,cty) -> F.fprintf fmt "%a%s" IP.pp f (cty_to_string cty)))
      conds
(*i*)

(* \ic{Convert the given [rpoly] to an oracle polynomial for
       parameters [params] and oracle random variables [orvars].} *)
let ipoly_to_opoly rvars params orvars p =
  let param_assoc = L.map (fun tid -> (tid.tid_id, tid)) params in
  let conv_var var =
    match var with 
    | NIVar id ->
      begin try
        Param(L.assoc id param_assoc)
      with
        Not_found ->
          if L.mem id orvars then ORVar(id)
          else if L.mem id rvars then SRVar(id)
          else failwith (fsprintf "variable %s not found in oracle definition" id)
      end
    | IVar _ -> assert false
  in
  IP.to_terms p |> OP.eval_generic OP.const (OP.var % conv_var)

(* \ic{Convert the given [rpoly] to a winning condition polynomial for
       choices [choices], oracle parameters [oparams], and polynomial [p].} *)
let ipoly_to_wpoly choices rvars oparams orvars p =
  let param_assoc   = L.map (fun tid -> (tid.tid_id, tid)) oparams in
  let choices_assoc = L.map (fun tid -> (tid.tid_id, tid)) choices in
  let conv_var v =
    match v with
    | NIVar v ->
      begin try
        Choice(L.assoc v choices_assoc)
      with Not_found ->
        if L.mem v rvars then RVar(v,Global)
        else
          failwith (fsprintf "non-indexed variable %s undefined in winning condition" v)
      end
    | IVar v ->
      begin try
        OParam(L.assoc v param_assoc)
      with Not_found ->
        if L.mem v orvars then RVar(v,Oracle)
        else failwith (fsprintf "indexed variable %s not found in winning condition" v)
      end
  in
  IP.to_terms p |> WP.eval_generic WP.const (WP.var % conv_var)

let ipoly_to_rpoly p =
  let conv_var = function NIVar id -> id | IVar _ -> assert false in
  IP.to_terms p |> RP.eval_generic RP.const (RP.var % conv_var)

(* \ic{Interpreter state for evaluating commands.} *)
type eval_state = {
  es_gs       : group_setting;
  es_inputs   : (rpoly * gid) list;
  es_varnames : id list;
  es_rvars    : id list;
  es_odefs    : odef list;
  es_oparams  : tid list;
  es_orvars   : id list;
  es_mwcond   : wcond option;
}

(* \ic{Initial (empty) interpreter state.} *)
let empty_eval_state = {
  es_gs       = { gs_isos = []; gs_emaps = [] };
  es_inputs   = [];
  es_varnames = [];
  es_rvars    = [];
  es_odefs    = [];
  es_oparams  = [];
  es_orvars   = [];
  es_mwcond   = None;
}  

let target_gids_of_estate estate =
  L.map (fun iso -> iso.iso_codom) estate.es_gs.gs_isos
  @ L.map (fun emap -> emap.em_codom) estate.es_gs.gs_emaps

(* \ic{Raise error if oracle definition invalid.} *)
let ensure_oracle_valid estate ovarnames params =
  if not (unique ovarnames)
    then failwith "Oracle reuses names for arguments/sampled variables.";
  if estate.es_odefs <> []
    then failwith "Oracle already defined, multiple oracles not supported.";
  let target_param =
    L.exists
      (fun gid -> L.mem (Group gid) (L.map (fun tid -> tid.tid_ty) params))
      (target_gids_of_estate estate)
  in
  if target_param
    then failwith "Oracle arguments that are target of isomorphism or map not supported yet."


(* \ic{Raise error if winning condition definition invalid.} *)
let ensure_winning_valid estate choices =
  let names = estate.es_varnames @ L.map (fun tid -> tid.tid_id) choices in
  if not (unique names) then failwith "Winning condition reuses names.";
  let target_choices =
    L.exists
      (fun gid -> L.mem (Group gid) (L.map (fun tid -> tid.tid_ty) choices))
      (target_gids_of_estate estate)
  in
  if target_choices
    then failwith "Oracle arguments that are target of isomorphism or map not supported yet."

(* \ic{Raise error if one of supposedly fresh vars included in used.} *)
let ensure_vars_fresh fresh used =
  L.iter
    (fun id ->
      if L.mem id used then
        failwith (fsprintf "sampled variable %s not fresh" id))
    fresh

(* \ic{Raise error if one of used vars not included in defined.} *)
let ensure_vars_defined used defined =
  L.iter
    (fun id ->
      if not (L.mem id defined) then
        failwith (fsprintf "used variable %s undefined (add sample X)" id))
    used

let ipoly_ids p = IP.vars p |> L.map (function NIVar id -> id | IVar id -> id)

(* \ic{Evaluate [cmd] in the interpreter state [estate] and
   return the updated interpreter state.} *)
let eval_cmd estate cmd =
  match cmd,estate.es_mwcond with
  | AddSamplings(ids),None ->
    ensure_vars_fresh ids estate.es_varnames;
    let varnames = estate.es_varnames @ ids in
    { estate with es_rvars = estate.es_rvars @ ids; es_varnames = varnames }
  | AddIsos(isos),None ->
    { estate with es_gs = { estate.es_gs with gs_isos = estate.es_gs.gs_isos@isos } }
  | AddMaps(emaps),None ->
    { estate with es_gs = { estate.es_gs with gs_emaps = estate.es_gs.gs_emaps@emaps } }
  | AddInput(fs,gid), None ->
    let used_vars = conc_map ipoly_ids fs in
    ensure_vars_defined used_vars estate.es_rvars;
    let varnames = sorted_nub compare (estate.es_varnames @ used_vars) in
    { estate with
      es_varnames = varnames;
      es_inputs = estate.es_inputs@(L.map (fun p -> (ipoly_to_rpoly p,gid)) fs) }
  | AddOracle(oname,params,orvars,fs), None ->
    let varnames =
      estate.es_varnames @ orvars @ L.map (fun tid -> tid.tid_id) params
    in
    ensure_oracle_valid estate varnames params;
    let od =
      { odef_name = oname;
        odef_return = L.map (fun (p, gid) -> (ipoly_to_opoly estate.es_rvars params orvars p,gid)) fs }
    in
    if estate.es_odefs <> [] then failwith "At most one oracle definition supported";
    { estate with
      es_odefs    = [od];
      es_oparams  = params;
      es_orvars   = orvars;
      es_varnames = varnames }
  | SetWinning(choices,conds), None ->
    ensure_winning_valid estate choices;
    let conv = ipoly_to_wpoly choices estate.es_rvars estate.es_oparams estate.es_orvars in
    let eqs,ineqs =
      partition_either
        (function (f,Eq) -> Left (conv f) | (f,InEq) -> Right (conv f))
        conds
    in
    { estate with
      es_mwcond = Some { wcond_ineqs = ineqs; wcond_eqs = eqs } }
  | _, Some _ ->
    failwith "Setting the winning condition must be the last command."

(* \ic{Evaluate the given commands and return the corresponding game
   definition.} *)
let eval_cmds cmds =
  let es =  List.fold_left eval_cmd empty_eval_state cmds in
  match es.es_mwcond with
  | None   ->
    failwith "no winning condition given"
  | Some wcond ->
    { gdef_inputs = es.es_inputs; gdef_odefs = es.es_odefs;
      gdef_wcond = wcond; gdef_gs = es.es_gs }
