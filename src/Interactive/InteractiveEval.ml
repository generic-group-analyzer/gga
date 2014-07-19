(*s Interpret commands for defining interactive problems. *)

(*i*)
open InteractiveInput
open Util

module F = Format
(*i*)

(*******************************************************************)
(* \hd{Commands to define games} *)

type cond_type = Eq | InEq

(* \ic{We use [rpoly]s for all types of commands and convert later on when
       we have all information required to distinguish the different types
       of variables.
       \begin{itemize}
       \item $AddIsos(isos)$: add isomorphisms to group setting.
       \item $AddMaps(isos)$: add maps to group setting.
       \item $AddInput(f)$: Add $f$ to adversary inputs.
       \item $AddOracle(on, tids, ids, rps)$: Add the oracle where the name
           is denoted by $on$,, the (typed) arguments are denoted by $tids$,
           the sampled random values are denoted by $ids$, and
           the returned polynomials together with the group identifier are
           denoted by $rps$.
       \item $SetWinning(tids, wps)$:
         Set the winning condition where winning condition polynomials
         together with ineq or eq are denoted by $wps$ and (typed) values chosen by
         the adversary are denoted by $tids$.
       \end{itemize}} *)
type cmd =
  | AddIsos    of iso list
  | AddMaps    of emap list
  | AddInput   of rpoly list * gid
  | AddOracle  of oname * tid list * id list * (rpoly * gid) list
  | SetWinning of tid list * (rpoly * cond_type) list

(*i*)
let pp_cmd fmt cmd =
  let cty_to_string = function Eq -> " = 0" | InEq -> " <> 0" in
  match cmd with
  | AddIsos isos ->
    F.fprintf fmt "isos: %a.\n" (pp_list ", " pp_iso) isos
  | AddMaps emaps ->
    F.fprintf fmt "maps: %a.\n" (pp_list ", " pp_emap) emaps
  | AddInput (fs,gid) ->
    F.fprintf fmt "add_input %a in %s\n" (pp_list "," RP.pp) fs gid
  | AddOracle(s,params,orvars,fs) ->
    F.fprintf fmt "add_oracle %s(%a) sample %a; (%a)" s
      (pp_list ", " pp_tid) params
      (pp_list ", " pp_string) orvars
      (pp_list ", "
         (fun fmt (rp,gid) -> F.fprintf fmt "%a in %a" RP.pp rp pp_ty (Group gid))) fs
  | SetWinning(choices,conds) ->
    F.fprintf fmt "set_winning (%a) cond: %a"
      (pp_list ", " pp_tid) choices
      (pp_list " /\\ "
         (fun fmt (f,cty) -> F.fprintf fmt "%a%s" RP.pp f (cty_to_string cty)))
      conds
(*i*)

(* \ic{Convert the given [rpoly] to an oracle polynomial for
       parameters [params] and oracle random variables [orvars].} *)
let rpoly_to_opoly params orvars p =
  let param_assoc = L.map (fun tid -> (tid.tid_id, tid)) params in
  let conv_var id =
    try
      Param(L.assoc id param_assoc)
    with
      Not_found ->
        if L.mem id orvars then ORVar(id)
        else SRVar(id)
  in
  RP.to_terms p |> OP.eval_generic OP.const (OP.var << conv_var)

(* \ic{Convert the given [rpoly] to a winning condition polynomial for
       choices [choices], oracle parameters [oparams], and polynomial [p].} *)
let rpoly_to_wpoly choices oparams p =
  let param_assoc   = L.map (fun tid -> (tid.tid_id, tid)) oparams in
  let choices_assoc = L.map (fun tid -> (tid.tid_id, tid)) choices in
  let conv_var v =
    try
      OParam(L.assoc v param_assoc)
    with
      Not_found ->
        try
          Choice(L.assoc v choices_assoc)
        with
          Not_found -> RVar(v)
  in
  RP.to_terms p |> WP.eval_generic WP.const (WP.var << conv_var)

type eval_state = {
  es_gs      : group_setting;
  es_inputs  : (rpoly * gid) list;
  es_odefs   : odef list;
  es_oparams : tid list;
  es_orvars  : id list;
  es_mwcond  : wcond option;
}

let empty_eval_state = {
  es_inputs  = [];
  es_odefs   = [];
  es_oparams = [];
  es_orvars  = [];
  es_gs      = { gs_isos = []; gs_emaps = [] };
  es_mwcond  = None;
}  

let eval_cmd estate cmd =
  match cmd,estate.es_mwcond with
  | AddIsos(isos),None ->
    { estate with es_gs = { estate.es_gs with gs_isos = estate.es_gs.gs_isos@isos } }
  | AddMaps(emaps),None ->
    { estate with es_gs = { estate.es_gs with gs_emaps = estate.es_gs.gs_emaps@emaps } }
  | AddInput(fs,gid), None ->
    { estate with es_inputs = estate.es_inputs@(L.map (fun p -> (p,gid)) fs) }
  | AddOracle(oname,params,orvars,fs), None ->
    if not (unique (L.map (fun tid -> tid.tid_id) params))
      then failwith "Two arguments with the same name in oracle definition";
    if not (unique orvars)
      then failwith "Oracle samples two random variables with the same name";
    if (L.exists (fun od -> od.odef_name = oname) estate.es_odefs)
      then failwith ("Oracle name used twice: "^oname);
    F.printf "%a\n" pp_cmd cmd;
    let od =
      { odef_name = oname;
        odef_return = L.map (fun (p, gid) -> (rpoly_to_opoly params orvars p,gid)) fs }
    in
    { estate with
      es_odefs   = estate.es_odefs@[od];
      es_oparams = estate.es_oparams@params;
      es_orvars  = estate.es_orvars@orvars
    }
  | SetWinning(choices,conds), None ->
    let conv = rpoly_to_wpoly choices estate.es_oparams in 
    let eqs,ineqs =
      partition_either
        (function (f,Eq) -> Left (conv f) | (f,InEq) -> Right (conv f))
        conds
    in
    { estate with
      es_mwcond = Some { wcond_ineqs = ineqs; wcond_eqs = eqs } }
  | _, Some _ ->
    failwith "Setting the winning condition must be the last command."

let eval_cmds cmds =
  let es =  List.fold_left eval_cmd empty_eval_state cmds in
  match es.es_mwcond with
  | None   ->
    failwith "no winning condition given"
  | Some wcond ->
    { gdef_inputs = es.es_inputs; gdef_odefs = es.es_odefs; gdef_wcond = wcond;
      gdef_gs = { gs_isos = []; gs_emaps = [] } }
