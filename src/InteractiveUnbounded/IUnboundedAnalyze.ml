(*s Analysis for interactive assumptions. *)

(*i*)
open Util
open Poly

open IUnbounded

module FS = IUnboundedFormalSum
module IR = IntRing
module II = IUnboundedInput
module RP = II.RP
module S = String
module YS = Yojson.Safe
(*i*)

(*********************************************************************)
(* \hd{Parsing game definitions} *)

(* \ic{Convert lexer and parser errors to error with meaningful message.} *)
let wrap_error f s =
  let sbuf = Lexing.from_string s in
  try
    f sbuf
  with
  | IUnboundedParser.Error ->
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
  | IUnboundedLexer.Error msg ->
    let pos = sbuf.Lexing.lex_curr_p in
    raise (failwith (F.sprintf "%s at %s:%d:%d"
                       msg
                       pos.Lexing.pos_fname
                       pos.Lexing.pos_lnum
                       (pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1)))

let p_cmds = wrap_error (IUnboundedParser.cmds_t IUnboundedLexer.lex)

(*********************************************************************)
(* \hd{Analyze game definitions} *)

let analyze_unbounded_from_string s = 
  let gdef = p_cmds s |> II.eval_cmds in
  F.printf "%a\n\n" II.pp_gdef gdef;
  let eq_constrs, ineq_constrs, qineq_constrs = IUnbounded.gdef_to_constrs gdef in
  
  F.printf "\n#########################################################\n";
  F.printf "Simplified constraints:\n\n";
  pp_constrs F.std_formatter eq_constrs ineq_constrs qineq_constrs;
  print_newline ();

  let pconstrs1 = (sorted_nub compare (L.map translate_eq eq_constrs) : YS.json list) in
  let pconstrs2 = sorted_nub compare (L.map translate_qineq qineq_constrs) in
  let pconstrs3 = sorted_nub compare (L.map translate_ineq ineq_constrs) in

  Z3_Solver.check_sat (pconstrs1 @ pconstrs2 @ pconstrs3)
