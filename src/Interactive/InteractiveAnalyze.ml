(*s Analysis for interactive assumptions. *)

(*i*)
open Util
open Poly

open InteractiveUnbounded

module FS = InteractiveFormalSum
module IR = IntRing
module II = InteractiveInput
module RP = II.RP
module S = String
(*i*)

(*********************************************************************)
(* \hd{Parsing game definitions} *)

(* \ic{Convert lexer and parser errors to error with meaningful message.} *)
let wrap_error f s0 =
  let s = S.copy s0 in
  let sbuf = Lexing.from_string s0 in
  try
    f sbuf
  with
  | InteractiveParser.Error ->
    let start = Lexing.lexeme_start sbuf in
    let err =
      Printf.sprintf
        "Syntax error at offset %d (length %d): \
         parsed ``%s'',\nerror at ``%s''"
        start
        (S.length s)
        (if start >= S.length s then s  else (S.sub s 0 start))
        (if start >= S.length s then "" else (S.sub s start (S.length s - start)))
    in
    print_endline err;
    failwith err
  | InteractiveLexer.Error msg ->
    let pos = sbuf.Lexing.lex_curr_p in
    raise (failwith (F.sprintf "%s at %s:%d:%d"
                       msg
                       pos.Lexing.pos_fname
                       pos.Lexing.pos_lnum
                       (pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1)))

let p_cmds = wrap_error (InteractiveParser.cmds_t InteractiveLexer.lex)

(*********************************************************************)
(* \hd{Analyze game definitions} *)

let analyze_bounded_from_string s bound = 
  let gdef = p_cmds s |> II.eval_cmds in
  F.printf "%a\n\n" II.pp_gdef gdef;
  let zero_constrs, nzero_constrs = InteractiveBounded.gdef_to_constrs bound gdef in
  let zcs = L.map Z3_Solver.poly_to_json zero_constrs in
  let nzcs =
    L.map (fun disj -> `List (L.map Z3_Solver.poly_to_json disj)) nzero_constrs
  in
  let vars =
    (L.concat nzero_constrs)@zero_constrs
    |> conc_map RP.vars
    |> sorted_nub compare
    |> L.map (fun v -> `String v)
  in
  flush stdout;
  let res = Sage_Solver.check_sat (`List zcs) (`List nzcs) (`List vars) in
  flush stdout;
  if res
    then F.printf "Assumption valid\n"
    else (
      let res = Z3_Solver.find_counter (`List zcs) (`List nzcs) in
      F.printf "%a\n" Z3_Solver.pp_result res
    );
  exit 0

let analyze_unbounded_from_string s = 
  let gdef = p_cmds s |> II.eval_cmds in
  F.printf "%a\n\n" II.pp_gdef gdef;
  let eq_constrs, ineq_constrs, qineq_constrs = InteractiveUnbounded.gdef_to_constrs gdef in
  
  F.printf "\n#########################################################\n";
  F.printf "Simplified constraints:\n\n";
  pp_constrs F.std_formatter eq_constrs ineq_constrs qineq_constrs;
  print_newline ();

  let pconstrs1 = sorted_nub compare (L.map translate_eq eq_constrs) in
  let pconstrs2 = sorted_nub compare (L.map translate_qineq qineq_constrs) in
  let pconstrs3 = sorted_nub compare (L.map translate_ineq ineq_constrs) in

  (*i List.iter (fun pc -> print_endline (YS.to_string pc)) (pconstrs1 @ pconstrs2 @ pconstrs3); i*)

  Z3_Solver.check_sat (pconstrs1 @ pconstrs2 @ pconstrs3)
