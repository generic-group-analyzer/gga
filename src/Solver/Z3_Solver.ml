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

module YS = Yojson.Safe
(*i*)

(* \ic{%
   [call_z3 cmd] calls Z3, outputs [cmd] to the standard input of
   Z3, and reads (up to) one line which is returned.} *)
let call_z3 cmd = call_external "/usr/bin/python scripts/ggt_z3.py" cmd 1

(* \ic{[poly_to_json f] creates a JSON representation of the polynomial [f].} *)
let poly_to_json f =
  `List
     (L.map
        (fun (m,c) ->
           `List [ `List (L.map (fun v -> `String v) m); `Int (Big_int.int_of_big_int c) ])
        (CP.to_terms f))

type result =
  | Attack of string
  | Valid
  | Unknown
  | Error of string

let pp_result fmt res =
  match res with
  | Attack s -> F.fprintf fmt "Attack found: %s" s
  | Error  s -> F.fprintf fmt "Error: %s" s
  | Valid    -> F.fprintf fmt "Assumption is valid."
  | Unknown  -> F.fprintf fmt "Z3 returned unknown."

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
  let err_comm = Error "Error communicating with Z3 wrapper." in
  match call_z3 (YS.to_string req^"\n") with
  | [sres] ->
    begin match YS.from_string sres with
    | `Assoc l -> 
      begin match L.assoc "ok" l with
      | `Bool true ->
        begin match L.assoc "res" l with
        | `String "sat"     -> Attack (get_string l "model")
        | `String "unsat"   -> Valid
        | `String "unknown" -> Unknown
        | _                 -> err_comm
        end
      | `Bool false -> Error (F.sprintf "Z3 wrapper returned an error: %s" (get_string l "error"))
      | _           -> err_comm
      end
    | _ -> err_comm
    end
  | _ -> err_comm
