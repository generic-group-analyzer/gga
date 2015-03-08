(*s Analysis for interactive assumptions. *)

(*i*)
open Util
open LPoly
open Big_int

module YS = Yojson.Safe

(* open InteractiveUnbounded *)

module FS = InteractiveFormalSum
module IR = IntRing
module II = InteractiveInput
module IE = InteractiveEval
module RP = II.RP
module S = String
(*i*)

(*********************************************************************)
(* \hd{Parsing game definitions} *)

(* \ic{Convert lexer and parser errors to error with meaningful message.} *)
let wrap_error f s =
  let sbuf = Lexing.from_string s in
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

(* \ic{[poly_to_json f] creates a JSON representation of the polynomial [f].} *)
let poly_to_json f =
  `List
     (L.map
        (fun (m,c) ->
           `List [ `List (conc_map (fun (v,e) -> replicate (`String v) e) m); `Int (int_of_big_int c) ])
        (RP.to_terms f))

let analyze_bounded_from_string ?(counter=true) ?(proof=true) ?(fmt=F.std_formatter) s bound = 
  let gdef = p_cmds s |> IE.eval_cmds in
  F.fprintf fmt "\n%a\n\n" II.pp_gdef gdef;
  let zero_constrs, nzero_constrs = InteractiveBounded.gdef_to_constrs fmt bound gdef in
  let zcs = L.map poly_to_json zero_constrs in
  let nzcs =
    L.map (fun disj -> `List (L.map poly_to_json disj)) nzero_constrs
  in
  let vars =
    (L.concat nzero_constrs)@zero_constrs
    |> conc_map RP.vars
    |> sorted_nub compare
    |> L.map (fun v -> `String v)
  in
  flush stdout;
  if not (counter || proof) then (
    Z3_Solver.Unknown ""
  ) else (
    let res = if counter then Z3_Solver.find_counter (`List zcs) (`List nzcs) else Z3_Solver.Unknown "no counter" in
    match res with
    | Z3_Solver.Attack _ -> res
    | _ when proof ->
      if Sage_Solver.is_contradictory (`List zcs) (`List nzcs) (`List vars)
      then Z3_Solver.Valid
      else Z3_Solver.Unknown "Sage returned unknown"
    | _ -> 
      Z3_Solver.Unknown "no attack, proof disabled"
  )

let analyze_unbounded_from_string _s =
  (*i
  let gdef = p_cmds s |> IE.eval_cmds in
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
  i*)
  Z3_Solver.check_sat [] (*i (pconstrs1 @ pconstrs2 @ pconstrs3) i*)
