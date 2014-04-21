(*s Main function of the ggt tool. *)

(*i*)
open Util
open Z3_Solver
(*i*)

let main =
  if Array.length Sys.argv <> 2 then
    output_string stderr (F.sprintf "usage: %s <inputfile>" Sys.argv.(0))
  else
    let scmds = Util.input_file Sys.argv.(1) in
    try
      let (res, info) = ParamAnalyze.analyze_from_string scmds in
      F.printf "%s\n\n%a\n" info pp_result res
    with
      ParamInput.InvalidAssumption err ->
        F.printf "Invalid assumption: %s" err

