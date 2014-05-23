(*s Analysis for interactive assumptions. *)

(*i*)
module S = String
(*i*)

(*********************************************************************)
(* \hd{Formal sums} *)



(*********************************************************************)
(* \hd{Unfolding formal sums given concrete bounds} *)



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
    raise (failwith (Printf.sprintf "%s" msg))

let p_cmds = wrap_error (InteractiveParser.cmds_t InteractiveLexer.lex)
