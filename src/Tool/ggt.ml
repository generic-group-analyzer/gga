(*s Main function of the ggt tool. *)

open Util

(*******************************************************************)
(* \subsection*{Main} *)

let main =
  if Array.length Sys.argv <> 2 then
    output_string stderr (F.sprintf "usage: %s <inputfile>" Sys.argv.(0))
  else
    let scmds = Util.input_file Sys.argv.(1) in
    ParametricAnalyze.analyze_from_string scmds
