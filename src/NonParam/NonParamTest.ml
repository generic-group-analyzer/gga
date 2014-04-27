(*s Tests for the non-parametric setting. *)

(*i*)
open OUnit
open NonParamInput
(*i*)


(*********************************************************************)
(* \hd{Tests} *)

let gs2 = {
  gs_isos = [ { iso_dom = "1"; iso_codom = "2"}
            ; { iso_dom = "1:2"; iso_codom = "3"} ];
  gs_emaps = [ { em_dom = ["1";"2"]; em_codom = "1:2"}
             ; { em_dom = ["3";"3"]; em_codom = "1"} ];
}

let test_cyclic s gs cyclic () =
  (*i*) (* F.printf "%a" pp_gs gs; *) (*i*)
  assert_equal ~msg:("cyclic check for "^s) (NonParamInput.Internals.gs_is_cyclic gs) cyclic

let tests =
  TestList
    [ "Non-parametric"  >:::
      [ "cyclic " >:: (test_cyclic "gs2" gs2 true) ] ]

let () =
  ignore (NonParamAnalyze.test ());
  ignore (run_test_tt_main tests)