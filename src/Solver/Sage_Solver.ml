(*s Sage solver for non-parametric and interactive problems.
    Calls a Python script that uses the Sage library
    and communicates using JSON over standard input and output.
    The Python scripts reads JSON command and returns a JSON command.
    It supports the following commands:
    \begin{verbatim}
    { 'cmd' : 'linSolve', 'M' : [[M1,1,..,M1,k],..,[Ml,1,..,Ml,k]],
      'b': [c1,...,ck] }\end{verbatim}
    and returns a JSON response of the form
    \begin{verbatim}
    { 'ok' :  true,
      'res' : 'sol'/'nosol',
      'sol' : '[s1,...,sl]' // included only for 'sol' }\end{verbatim}
    %
    or \verb!{ 'ok' :  false, 'error' : 'foo went wrong' }! in case of
    error. \\
    \begin{verbatim}
    { 'cmd' : 'leftKernel', 'M' : [[M1,1,..,M1,k],..,[Ml,1,..,Ml,k]] }\end{verbatim}
    and returns a JSON response of the form
    \begin{verbatim}
    { 'ok' :  true,
      'res' : [[k1_1,...,k1_l],...] }\end{verbatim}
    %
    or \verb!{ 'ok' :  false, 'error' : 'foo went wrong' }! in case of
    error.
*)

(*i*)
(* open ParamConstraints *)
open Util
open Big_int

module YS = Yojson.Safe
(*i*)

let call_Sage cmd = call_external "./scripts/ggt_Sage.py" cmd 1

let get_string l k =
  try  match L.assoc k l with 
       | `String s -> s
       | _ -> raise Not_found
  with Not_found -> k^" not found" 

let get_vec l k = 
  match L.assoc k l with 
  | `List v -> L.map (function `Int i -> i | _ -> raise Not_found) v
  | _       -> raise Not_found

let get_list f l k = 
  match L.assoc k l with
  | `List xs -> L.map (function `List ys -> L.map f ys | _ -> raise Not_found) xs
  | _       -> raise Not_found

let vec_to_json v = `List (L.map (fun i -> `Int (int_of_big_int i)) v)

let mat_to_json m = `List (L.map (fun v -> vec_to_json v) m)

let lin_solve m b =
  let mr = mat_to_json m in
  let br = vec_to_json b in
  let req = `Assoc [ ("cmd",`String "linSolve"); ("M",mr); ("b",br) ] in
  match call_Sage (YS.to_string req^"\n") with
  | [sres] ->
    begin match YS.from_string sres with
    | `Assoc l -> 
      begin match L.assoc "ok" l with
      | `Bool true ->
        begin match L.assoc "res" l with
        | `String "sol"     -> Some(get_vec l "sol")
        | `String "nosol"   -> None
        | _                 -> failwith "SAGE"
        end
      | `Bool false ->
        failwith (F.sprintf "Sage wrapper returned an error: %s" (get_string l "error"))
      | _ -> failwith "SAGE"
      end
    | _ -> failwith "SAGE"
    end
  | _ -> failwith "SAGE"

let compare_kernel lm rm =
  let lmj = mat_to_json lm in
  let rmj = mat_to_json rm in
  let req = `Assoc [ ("cmd",`String "compareKernel"); ("LM",lmj); ("RM",rmj) ] in
  match call_Sage (YS.to_string req^"\n") with
  | [sres] ->
    begin match YS.from_string sres with
    | `Assoc l -> 
      begin match L.assoc "ok" l with
      | `Bool true ->
        let lk = get_list (function `Int i -> i | _ -> raise Not_found) l "LK" in
        let rk = get_list (function `Int i -> i | _ -> raise Not_found) l "RK" in
        let lonly = get_list (function `Int i -> i | _ -> raise Not_found) l "lonly" in
        let ronly = get_list (function `Int i -> i | _ -> raise Not_found) l "ronly" in
        let bad_primes = get_vec l "bad_primes" in
        (lk, rk, lonly, ronly, bad_primes)
      | `Bool false ->
        failwith (F.sprintf "Sage wrapper returned an error: %s" (get_string l "error"))
      | _ ->
        failwith "SAGE"
      end
    | _ -> failwith "SAGE"
    end
  | _ -> failwith "SAGE"

(*
let () =
  (* FIXME: add exit handlers for other systems, also kill Sage if it does not react. *)
  let exit_cmd = YS.to_string (`Assoc [ ("cmd", `String "exit") ])^"\n" in
  at_exit (fun () -> if is_started Sage then ignore (call_system Sage exit_cmd 1))
*)