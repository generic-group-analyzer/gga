open InteractiveInput
open Util

module F = Format

(*******************************************************************)
(* \hd{Commands to define games} *)

type cond_type = Eq | InEq

(* \ic{We use [rpoly]s for all types of commands and convert later on when
       we have all information required to distinguish the different types
       of variables.
       \begin{itemize}
      \item $AddInput(f)$
       \end{itemize}} *)
type cmd =
  | AddInput   of rpoly list
  | AddOracle  of oname * tid list * id list * rpoly list
  | SetWinning of tid list * (rpoly * cond_type) list

(*i*)
let pp_cmd fmt cmd =
  let cty_to_string = function Eq -> " = 0" | InEq -> " <> 0" in
  match cmd with
  | AddInput fs ->
    F.fprintf fmt "add_input %a" (pp_list "," RP.pp) fs
  | AddOracle(s,params,orvars,fs) ->
    F.fprintf fmt "add_oracle %s(%a) sample %a; (%a)" s
      (pp_list ", " pp_tid) params
      (pp_list ", " pp_string) orvars
      (pp_list ", " RP.pp) fs
  | SetWinning(choices,conds) ->
    F.fprintf fmt "set_winning (%a) cond: %a"
      (pp_list ", " pp_tid) choices
      (pp_list " /\\ "
         (fun fmt (f,cty) -> F.fprintf fmt "%a%s" RP.pp f (cty_to_string cty)))
      conds
(*i*)

(*
(* \ic{Convert the given [rpoly] to an oracle polynomial for
       parameters [params] and oracle random variables [orvars].} *)
let rpoly_to_opoly (params : tid list) (orvars : id list) p =
  let conv_var tid =
    if L.mem tid params then Param(tid)
    else if L.mem tid orvars then ORVar(tid)
    else SRVar(tid)
  in
  RP.to_terms p
  |> L.map (fun (m,c) -> (L.map conv_var m, c))
  |> OP.from_terms
*)

(*
(* \ic{Convert the given [rpoly] to a winning condition polynomial for
       choices [choices], oracle parameters [oparams], and polynomial [p].} *)
let rpoly_to_wpoly choices oparams p =
  (* utility functions *)
  let fchoices = conc_map (function (v,Field) -> [v] | _ -> []) choices in
  let gchoices = conc_map (function (v,Group) -> [v] | _ -> []) choices in
  let has_group_choice = ref false in
  let has_oparam       = ref false in  
  let conv_var v =
    if L.mem v oparams then (has_oparam := true; OFParam(v))
    else if L.mem v fchoices then FieldChoice(v)
    else if L.mem v gchoices then (has_group_choice := true; GroupChoice(v))
    else RVar(v)
  in
  if !has_oparam && !has_group_choice then
    failwith "Polynomials that contain both oracle parameter and group choice not supported";
  RP.to_terms p
  |> L.map (fun (m,c) -> (L.map conv_var m, c))
  |> WP.from_terms
*)

type eval_state = {
  es_inputs  : rpoly list;
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
  es_mwcond  = None;
}  

let eval_cmd estate cmd =
  (* let gvars = conc_map (fun f -> RP.vars f) inputs0 |> sorted_nub compare in *)
  match cmd,estate.es_mwcond with
  | AddInput fs, None ->
    { estate with es_inputs = estate.es_inputs@fs }
  | AddOracle(oname,params,orvars,fs), None ->
    if not (unique (L.map (fun tid -> tid.tid_id) params))
      then failwith "Two arguments with the same name in oracle definition";
    if not (unique orvars)
      then failwith "Oracle samples two random variables with the same name";
    if (L.exists (fun od -> od.odef_name = oname) estate.es_odefs)
      then failwith ("Oracle name used twice: "^oname);
    F.printf "%a\n" pp_cmd cmd;
    { estate with
      es_odefs   = estate.es_odefs@[] (* [ (oname, L.map (rpoly_to_opoly gvars params orvars) fs) ]*);
      es_oparams = estate.es_oparams@params;
      es_orvars  = estate.es_orvars@orvars
    }
  | SetWinning(choices,conds), None ->
    (*i
    let conv = rpoly_to_wpoly gvars choices oparams0 in
    let ineqs = conc_map (function (f,InEq) -> [ conv f ] | (_,Eq)   -> []) conds in
    let eqs   = conc_map (function (f,Eq)   -> [ conv f ] | (_,InEq) -> []) conds in
    i*)
    let ineqs = [] in
    let eqs = [] in
    { estate with
      es_mwcond = Some { wcond_ineqs = ineqs; wcond_eqs = eqs } }
  | _, Some _ ->
    failwith "Setting the winning condition must be the last command"

let eval_cmds cmds =
  let es =  List.fold_left eval_cmd empty_eval_state cmds in
  match es.es_mwcond with
  | None   ->
    failwith "no winning condition given"
  | Some wcond ->
    { gdef_inputs = es.es_inputs; gdef_odefs = es.es_odefs; gdef_wcond = wcond }
