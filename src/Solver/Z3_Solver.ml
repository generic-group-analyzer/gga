(*s Z3 solver for constraints derived from parametric problem.
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

module YS = Yojson.Safe
(*i*)


(* \ic{%
   [call_z3 cmd linenum] calls Z3, outputs [cmd] to the standard input of
   Z3, and reads (up to) [linenum] lines which are returned.} *)
let call_z3 cmd linenum =
  let (c_in, c_out) = Unix.open_process "/usr/bin/python scripts/ggt_z3.py" in
  output_string c_out cmd;
  flush c_out;
  let rec loop o linenum =
    if linenum = 0 then o
    else (
      try
        let l = input_line c_in in
        loop (o @ [l]) (linenum - 1)
      with End_of_file ->
        ignore (Unix.close_process (c_in,c_out));
        o)
  in loop [] linenum

(* \ic{[poly_to_json f] creates a JSON representation of the polynomial [f].} *)
let poly_to_json f =
  `List
     (L.map
        (fun (m,c) ->
           `List [ `List (L.map (fun v -> `String v) m); `Int (Big_int.int_of_big_int c) ])
        (CP.to_terms f))

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
  let get_string l k =
    try  match L.assoc k l with 
         | `String s -> s
         | _ -> raise Not_found
    with Not_found -> k^" not found" 
  in
  match call_z3 (YS.to_string req^"\n") 1 with
  | [sres] ->
    begin match YS.from_string sres with
    | `Assoc l -> 
      begin match L.assoc "ok" l with
      | `Bool true ->
        begin match L.assoc "res" l with
        | `String "sat"     -> F.sprintf "There is an attack:\n %s" (get_string l "model")
        | `String "unsat"   -> F.sprintf "The assumption is valid."
        | `String "unknown" -> F.sprintf "Z3 returned unknown"
        | _                 -> F.sprintf "Error communicating with Z3."
        end
      | `Bool false -> F.sprintf "Z3 wrapperreturned an error: %s" (get_string l "error")
      | _           -> F.sprintf "Error communicating with Z3."
      end
    | _ -> F.sprintf "Error communicating with Z3."
    end
  | _ -> F.sprintf "Expected one line."
