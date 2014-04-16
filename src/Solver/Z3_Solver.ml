open Parametric_Constr

module YS = Yojson.Safe

let call_z3 cmd linenum =
  let (c_in, c_out) = Unix.open_process "/usr/bin/python scripts/ggt_z3.py" in
  output_string c_out cmd;
  (* F.printf "input: `%s' has been sent\n\n%!" cmd; *)
  flush c_out;
  let rec loop o linenum =
    if linenum = 0 then o
    else (
      try
        let l = input_line c_in in
        (* F.printf "output: `%s'\n%!" l; *)
        loop (o @ [l]) (linenum - 1)
      with End_of_file ->
        ignore (Unix.close_process (c_in,c_out));
        o)
  in loop [] linenum

let poly_to_json f =
  let ts = ConstrPoly.to_terms f in
  `List (List.map (fun (c,m) -> `List [ `Int c; `List (List.map (fun v -> `String v) m) ]) ts)

let solve constrs =
  let trans a b = `List [poly_to_json a; poly_to_json b] in
  let eqs  =
    List.concat (List.map (function (a,b,Eq,_)  -> [trans a b] | (_,_,Leq,_) -> []) constrs)
  in
  let leqs =
    List.concat (List.map (function (a,b,Leq,_) -> [trans a b] | (_,_,Eq,_) -> [])  constrs)
  in
  let req = `Assoc [ ("cmd", `String "paramSolve")
                   ; ("eqs", `List eqs)
                   ; ("leqs", `List leqs)
                   ]
  in
  match call_z3 (YS.to_string req^"\n") 1 with
  | [sres] ->
    begin match YS.from_string sres with
    | `Assoc l -> 
      let ok = List.assoc "ok" l in
      let res = List.assoc "res" l in
      begin match ok, res with
      | `Bool true, `String "sat" ->
        F.printf "There is an attack:\n %s"
          (match List.assoc "model" l with `String s -> s | _ -> "no model returned")
      | `Bool true, `String "unsat" ->
        F.printf "The assumption is valid."
      | `Bool true, `String "unknown" ->
        F.printf "Z3 returned unknown"
      | _ ->
        F.printf "Error returned by Z3."
      end
    | _ -> 
      F.printf "Error communicating with Z3."
    end
  | _ -> 
    F.printf "Expected one line."
