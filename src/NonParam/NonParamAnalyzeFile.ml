(*s Analyze assumptions from file *)

(*i*)
open Util
open NonParamInput
open NonParamAnalyze

module S = String
(*i*)

(* \ic{Convert lexer and parser errors to error with meaningful message.} *)
let wrap_error f s0 =
  let s = S.copy s0 in
  let sbuf = Lexing.from_string s0 in
  try
    f sbuf
  with
  | NonParamParser.Error ->
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
  | NonParamLexer.Error msg ->
    raise (failwith (Printf.sprintf "%s" msg))
  | InvalidAssumption _ as e->
    raise e
  | _ ->
    failwith "Unknown error while lexing/parsing."

let p_cmds = wrap_error (NonParamParser.cmds_t NonParamLexer.lex)

let analyze_from_string scmds = scmds |> p_cmds |> eval_cmds |> analyze

let analyze_file fn = input_file fn |> analyze_from_string
