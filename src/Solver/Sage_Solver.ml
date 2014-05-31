(*s Sage solver for non-parametric and interactive problems.
    Calls a Python script that uses the Sage library
    and communicates using JSON over standard input and output.
*)

(*i*)
open Util
open Big_int

module YS = Yojson.Safe
(*i*)

let call_Sage cmd = call_external "./scripts/ggt_Sage.py" cmd 1 |> L.hd

let vec_to_json v = `List (L.map (fun i -> `Int (int_of_big_int i)) v)

let mat_to_json m = `List (L.map (fun v -> vec_to_json v) m)

let lin_solve m b =
  let mr = mat_to_json m in
  let br = vec_to_json b in
  let req = `Assoc [ ("cmd",`String "linSolve"); ("M",mr); ("b",br) ] in
  let sres = call_Sage (YS.to_string req^"\n") in
  let mres = YS.from_string sres in
  if get_assoc "ok" mres |> get_bool
    then
      begin match get_assoc "res" mres |> get_string with
      | "sol"     -> Some(get_assoc "sol" mres |> get_vec)
      | "nosol"   -> None
      | _         -> failwith "lin_solve: Sage wrapper returned unknown 'res' value"
      end
    else
      failwith
        ("lin_solve: Sage wrapper returned an error: "^
         (get_assoc "error" mres |> get_string))

let compare_kernel lm rm =
  let lmj = mat_to_json lm in
  let rmj = mat_to_json rm in
  let req = `Assoc [ ("cmd",`String "compareKernel"); ("LM",lmj); ("RM",rmj) ] in
  let sres = call_Sage (YS.to_string req^"\n") in
  let mres = YS.from_string sres in
  if get_assoc "ok" mres |> get_bool
    then (
      let lk      = get_assoc "LK" mres      |> get_matrix in
      let rk      = get_assoc "RK" mres      |> get_matrix in
      let exc_ub  = get_assoc "exc_ub" mres  |> get_int in
      let attacks =
        get_assoc "attacks" mres |> get_list (get_pair get_bool (get_list get_int))
      in
      (lk, rk, exc_ub, attacks)
    ) else (
      failwith
        ("compare_kernel: Sage wrapper returned an error: "^
         (get_assoc "error" mres |> get_string))
    )

let check_sat zero_constrs nzero_constrs vars =
  let req = 
    `Assoc [ ("cmd",`String "checkSat")
           ; ("zero",zero_constrs)
           ; ("nzero",nzero_constrs)
           ; ("vars", vars)]
  in
  let sres = call_Sage (YS.to_string req^"\n") in
  let mres = YS.from_string sres in
  if get_assoc "ok" mres |> get_bool
    then (
      get_assoc "contradictory" mres |> get_bool
    ) else (
      failwith
        ("compare_kernel: Sage wrapper returned an error: "^
         (get_assoc "error" mres |> get_string))
    )
