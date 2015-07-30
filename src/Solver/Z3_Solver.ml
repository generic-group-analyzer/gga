(* This file is distributed under the MIT License (see LICENSE). *)

(*s Z3 solver for constraints derived from parametric problems.
    Calls a Python script that uses the Python Z3 bindings
    and communicates using JSON over standard input and output.
    The Python scripts reads a JSON command of the form
    \begin{verbatim}
    { 'cmd' : 'paramSolve', 'eqs' : [[a1,b1],..], 'leqs': [[c1,d1],..] }\end{verbatim}
    and returns a JSON response of the form
    \begin{verbatim}
    { 'ok' :  true,
      'res' : 'sat'/'unsat'/'unknown',
      'model' : '[ x = 1, ...]' // included only for 'sat' }\end{verbatim}
    %
    or \verb!{ 'ok' :  false, 'error' : 'foo went wrong' }! in case of
    error.
*)

(*i*)
open ParamConstraints
open Util
open Big_int

module YS = Yojson.Safe
(*i*)

(* \ic{%
   [call_z3 cmd] calls Z3, outputs [cmd] to the standard input of
   Z3, and reads (up to) one line which is returned.} *)
let call_z3 cmd = call_external "/usr/bin/python scripts/ggt_z3.py" cmd 1 |> L.hd

(* \ic{[poly_to_json f] creates a JSON representation of the polynomial [f].} *)
let poly_to_json f =
  `List
     (L.map
        (fun (m,c) ->
           `List [ `List (L.map (fun v -> `String v) m); `Int (int_of_big_int c) ])
        (CP.to_terms f))

type result =
  | Attack of string
  | Valid
  | Unknown of string
  | Error of string

let pp_result fmt res =
  match res with
  | Attack s  -> F.fprintf fmt "Attack:\n%s\nAttack found (see above)." s
  | Error  s  -> F.fprintf fmt "Error: %s" s
  | Valid     -> F.fprintf fmt "Assumption is valid."
  | Unknown s -> F.fprintf fmt "Z3 returned unknown: %s" s

(* \ic{[solve constrs] solves the given list of constraints using Z3.} *)
let solve constrs =
  let trans a b = `List [poly_to_json a; poly_to_json b] in
  let eqs  =
    conc_map (function (a,Eq,b,_)  -> [trans a b] | (_,Leq,_,_) -> []) constrs
  in
  let leqs =
    conc_map (function (a,Leq,b,_) -> [trans a b] | (_,Eq,_,_) -> []) constrs
  in
  let req =
    `Assoc [ ("cmd", `String "paramSolve"); ("eqs", `List eqs); ("leqs", `List leqs) ]
  in
  let sres = call_z3 (YS.to_string req^"\n") in
  let mres = YS.from_string sres in
  if get_assoc "ok" mres |> get_bool
  then
    begin match get_assoc "res" mres |> get_string with
    | "sat"     -> Attack (get_assoc "model" mres |> get_string)
    | "unsat"   -> Valid
    | "unknown" -> Unknown ""
    | _         -> Error "Error communicating with Z3 wrapper, expected sat/unsat/unknown."
    end
  else
    Error ("Z3 wrapper returned an error:"^(get_assoc "error" mres |> get_string))

let check_sat constrs =
  let req =
    `Assoc [ ("cmd", `String "checkSat"); ("constrs", `List constrs) ]
  in
  let sres = call_z3 (YS.to_string req^"\n") in
  let mres = YS.from_string sres in
  if get_assoc "ok" mres |> get_bool
  then
    begin match get_assoc "res" mres |> get_string with
    | "sat"     -> Attack (get_assoc "model" mres |> get_string)
    | "unsat"   -> Valid
    | "unknown" -> Unknown ""
    | _         -> Error "Error communicating with Z3 wrapper, expected sat/unsat/unknown."
    end
  else
    Error ("Z3 wrapper returned an error:"^(get_assoc "error" mres |> get_string))

let find_counter zero_constrs nzero_constrs  =
  let req =
    `Assoc [ ("cmd", `String "boundedCounter"); ("zero", zero_constrs); ("nzero", nzero_constrs) ]
  in
  let sres = call_z3 (YS.to_string req^"\n") in
  let mres = YS.from_string sres in
  if get_assoc "ok" mres |> get_bool
  then
    begin match get_assoc "res" mres |> get_string with
    | "sat"     -> Attack (get_assoc "model" mres |> get_string)
    | "unsat"   -> Valid
    | "unknown" -> Unknown ""
    | _         -> Error "Error communicating with Z3 wrapper, expected sat/unsat/unknown."
    end
  else
    Error ("Z3 wrapper returned an error:"^(get_assoc "error" mres |> get_string))
