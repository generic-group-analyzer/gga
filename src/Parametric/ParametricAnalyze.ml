(*s Parametric assumption analysis: parsing wrappers and analysis. *)

(*i*)
open Util
open ParametricInput
open ParametricConstraints

module S = String
(*i*)

(*******************************************************************)
(* \hd{Parsing} *)

(* \ic{Convert lexer and parser errors to ParseError exception.} *)
let wrap_error f s0 =
  let s = S.copy s0 in
  let sbuf = Lexing.from_string s0 in
  try
    f sbuf
  with
  | Parser.Error ->
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
  | Lexer.Error msg ->
    raise (failwith (Printf.sprintf "%s" msg))
  | InvalidAssumption s ->
    failwith ("Invalid assumption: "^s)
  | _ ->
    failwith "Unknown error while lexing/parsing."

let p_cmds = wrap_error (Parser.cmds_t Lexer.lex)

(*******************************************************************)
(* \newpage\hd{Analyzer} *)

let analyze assm =
  let inps = assm.ca_inputs in
  F.printf "%a" pp_inputs inps;
  let chal = assm.ca_challenge in
  F.printf "%a" pp_challenge chal;

  let constrs = gen_constrs inps chal assm.ca_arity in
  F.printf "constraints:\n  %a\n" (pp_list "\n  " pp_constr) constrs;
  print_newline ();
  Z3_Solver.solve constrs;
  print_newline ()

let analyze_from_string scmds =
  let cmds  = p_cmds scmds in
  analyze (close_assumption (eval_cmds cmds))