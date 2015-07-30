(* This file is distributed under the MIT License (see LICENSE). *)

(*s Parametric assumption analysis: parsing wrappers and analysis. *)

(*i*)
open ParamInput
open ParamConstraints
open Util

module S = String
(*i*)

(*******************************************************************)
(* \hd{Parsing} *)

(* \ic{Convert lexer and parser errors to error with meaningful message.} *)
let wrap_error f s =
  let sbuf = Lexing.from_string s in
  try
    f sbuf
  with
  | ParamParser.Error ->
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
  | ParamLexer.Error msg ->
    raise (failwith (Printf.sprintf "%s" msg))
  | InvalidAssumption _ as e->
    raise e
  | _ ->
    failwith "Unknown error while lexing/parsing."

let p_cmds = wrap_error (ParamParser.cmds_t ParamLexer.lex)

(*******************************************************************)
(* \newpage\hd{Analyzer} *)

let analyze fmt assm =
  let inps = assm.ca_inputs in
  let chal = assm.ca_challenge in
  let constrs = gen_constrs assm.ca_problem_type inps chal assm.ca_arity in

  F.fprintf fmt "%a" pp_inputs inps;
  F.fprintf fmt "%a" pp_challenge chal;
  F.fprintf fmt "constraints:\n  %a\n%!" (pp_list "\n  " pp_constr) constrs;

  Z3_Solver.solve constrs

let analyze_from_string fmt scmds =
  let cmds  = p_cmds scmds in
  analyze fmt (close_assumption (eval_cmds cmds))
