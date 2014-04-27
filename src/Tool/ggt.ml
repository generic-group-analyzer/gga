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
      let res = ParamAnalyze.analyze_from_string F.err_formatter scmds in
      F.printf "%a\n" pp_result res
    with
      ParamInput.InvalidAssumption err ->
        F.printf "Invalid assumption: %s" err
