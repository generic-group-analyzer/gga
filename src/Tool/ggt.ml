(*s Main function of the ggt tool. *)

(*i*)
open Util

module S = String
(*i*)

let main_analyze () = 
  if Array.length Sys.argv <> 3 then
    output_string stderr (F.sprintf "usage: %s <param|nonparam|interactive|interactive_i|synth> <inputfile>\n" Sys.argv.(0))
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
    | "interactive" ->
      let open InteractiveAnalyze in
      begin try
        let res = analyze_unbounded_from_string scmds in
        F.printf "%a\n" Z3_Solver.pp_result res
      with
        InteractiveInput.InvalidAssumption err ->
          F.printf "Invalid assumption: %s\n" err
      end
    | s when S.sub s 0 (S.length "interactive_") = "interactive_" ->
      let pref = "interactive_" in
      let remainder = S.sub s (S.length pref) (S.length s - S.length pref) in
      let bound = try int_of_string remainder with Failure _ -> 3 in
      let open InteractiveAnalyze in
      begin try
        F.printf "bound set to %i\n" bound;

        let res = analyze_bounded_from_string scmds bound in
        F.printf "%a\n" Z3_Solver.pp_result res;
        match res with
        | Z3_Solver.Valid ->
          exit 0
        | Z3_Solver.Attack _ ->
          exit 1
        | _ ->
          exit 2
      with
        InteractiveInput.InvalidAssumption err ->
          F.printf "Invalid assumption: %s\n" err
      end
    | s when S.sub s 0 (S.length "interactivep_") = "interactivep_" ->
      let pref = "interactivep_" in
      let remainder = S.sub s (S.length pref) (S.length s - S.length pref) in
      let bound = try int_of_string remainder with Failure _ -> 3 in
      let open InteractiveAnalyze in
      begin try
        F.printf "bound set to %i\n" bound;

        let res = analyze_bounded_from_string ~counter:false scmds bound in
        F.printf "%a\n" Z3_Solver.pp_result res;
        match res with
        | Z3_Solver.Valid ->
          exit 0
        | _ ->
          exit 2
      with
        InteractiveInput.InvalidAssumption err ->
          F.printf "Invalid assumption: %s\n" err
      end

    | s when S.sub s 0 (S.length "interactivea_") = "interactivea_" ->
      let pref = "interactivea_" in
      let remainder = S.sub s (S.length pref) (S.length s - S.length pref) in
      let bound = try int_of_string remainder with Failure _ -> 3 in
      let open InteractiveAnalyze in
      begin try
        F.printf "bound set to %i\n" bound;

        let res = analyze_bounded_from_string ~proof:false scmds bound in
        F.printf "%a\n" Z3_Solver.pp_result res;
        match res with
        | Z3_Solver.Attack _ ->
          exit 1
        | _ ->
          exit 2
      with
        InteractiveInput.InvalidAssumption err ->
          F.printf "Invalid assumption: %s\n" err
      end

    | s ->
      F.printf "Invalid command: %s\n" s

let main =
  match Sys.argv.(1) with
  | ("synth" | "count") as s ->
    SynthesisCmd.synth (s = "count") (try Sys.argv.(2) with _ -> "II")

  | "test"  -> Unbounded.test ()
  | _       -> main_analyze ()
