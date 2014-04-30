(*s Main function of the ggt tool. *)

(*i*)
open Util
(*i*)

let main =
  if Array.length Sys.argv <> 3 then
    output_string stderr (F.sprintf "usage: %s <param|nonparam> <inputfile>" Sys.argv.(0))
  else
    let scmds = Util.input_file Sys.argv.(2) in
    match Sys.argv.(1) with
    | "param" ->
      let open Z3_Solver in
      begin try
        let res = ParamAnalyze.analyze_from_string F.err_formatter scmds in
        F.printf "%a\n" pp_result res
      with
        ParamInput.InvalidAssumption err ->
          F.printf "Invalid assumption: %s\n" err
      end
    | "nonparam" ->
      let open NonParamAnalyze in
      begin try
        let res = analyze_from_string scmds in
        F.printf "%a\n" pp_result_info res;
        F.printf "%a\n" pp_result res
      with
        NonParamInput.InvalidAssumption err ->
          F.printf "Invalid assumption: %s\n" err
      end
    | s ->
      F.printf "Invalid command: %s\n" s

