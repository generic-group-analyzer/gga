open Util
open Parametric_Input
open Parametric_Constr

module S = String
module F = Format

(*******************************************************************)
(* Parsing *)

(** Convert lexer and parser errors to ParseError exception *)
let wrap_error f s0 =
  let s = S.copy s0 in
  let sbuf = Lexing.from_string s0 in
  try
    f sbuf
  with
  | Lexer.Error msg ->
      raise (failwith (Printf.sprintf "%s%!" msg))
  | Parser.Error ->
      let start = Lexing.lexeme_start sbuf in
      let err = Printf.sprintf
                  "Syntax error at offset %d (length %d): parsed ``%s'',\nerror at ``%s''"
                  start
                  (S.length s)
                  (if start >= S.length s then s  else (S.sub s 0 start))
                  (if start >= S.length s then "" else (S.sub s start (S.length s - start)))
      in
      print_endline err;
      failwith err
  | _ -> failwith "Unknown error while lexing/parsing."

let p_rexpr = wrap_error (Parser.rexpr_t Lexer.lex)

let p_input_line = wrap_error (Parser.inputs_t Lexer.lex)

let p_challenge = wrap_error (Parser.challenge_t Lexer.lex)

(*******************************************************************)
(* Analyzer *)

let analyze sinput schallenge =
  let inp = p_input_line sinput in
  F.printf "input: @\n  %a@\n@\n"
    (pp_list "@\n  " (fun fmt (i,re) -> Format.fprintf fmt "%i: %a" i pp_rexpr_level re))
    (mapi' (fun i inp -> (i,inp)) inp);
  let chal = p_challenge schallenge in
  F.printf "challenge: %a @@ level %a\n\n" pp_input_monomial (snd chal) pp_level (fst chal);
  let constrs = gen_constrs inp chal in
  F.printf "constraints:\n  %a\n" (pp_list "\n  " pp_constr) constrs;
  print_newline ();
  Z3_Solver.solve constrs;
  print_newline ()

(*******************************************************************)
(* Tests *)

let sinput = "\
input \
  [ 1\
  , Y\
  , forall i in [0,l1]: X^i\
  , forall j in [0,l1 - 2]: X^(l1 + 2 + j) ] @ 1."

let schallenge = "challenge Y*X^(l1 + 1) @ 2."

let () =
  analyze sinput schallenge

(*
let stheory = "\
setting symmetric.  (* symmetric (non-leveled) k-linear map *)\
arity 2.            (* fixes the arity k to 2 *)\
problem decisional. (* we handle decisional and computational problems *)\
\
input\
  [ 1\
  , Y\
  , forall i in [0,l1]: X^i\
  , forall j in [0,l1 - 2]: X^(l1 + 2 + j) ] @ 1.\
\
challenge Y*X^(l1 + 1) @ k."
*)





