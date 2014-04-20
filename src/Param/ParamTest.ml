(*s Tests for parametric assumption analysis: see \verb!tests/param! for test input. *)
open ParamAnalyze
open ParamInput
open Util
open OUnit
open Z3_Solver

let testdir = "tests/param"

(*********************************************************************)
(* \hd{Test files} *)

let ggt_re = Str.regexp_string ""

let list_files dir =
  Array.to_list (Sys.readdir dir)
    |> List.filter (fun s -> Str.string_match ggt_re s 0)
    |> List.map (fun fn -> dir^"/"^fn)

let valid_files  = list_files (testdir^"/valid")
let attack_files = list_files (testdir^"/attack")
let error_files  = list_files (testdir^"/error")

(*********************************************************************)
(* \hd{Tests} *)

let analyze_file fn = fn |> input_file |> analyze_from_string |> fst

let test_valid fn () =
  assert_equal ~msg:("valid "^fn) (analyze_file fn) Valid

let test_attack fn () =
  assert_bool
    ("attack "^fn)
    (match analyze_file fn with Attack _ -> true | _ -> false)

let test_error fn () =
  assert_bool 
    ("error "^fn)
    (try ignore (analyze_file fn); false with InvalidAssumption _ -> true)

let analyze_tests =
  TestList
    [ "Valid"  >:::
      (L.map (fun fn -> ("valid("^fn^")")   >:: test_valid fn)  valid_files)
    ; "Attack" >:::
      (L.map (fun fn -> ("attack("^fn^")") >:: test_attack fn) attack_files)
    ; "Error"  >:::
      (L.map (fun fn -> ("error("^fn^")")  >:: test_error fn)  error_files)
    ]

let () =
  ignore (run_test_tt_main analyze_tests)