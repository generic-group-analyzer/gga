(*s Tests for the non-parametric setting. *)

(*i*)
open OUnit
open NonParamInput
open NonParamCompletion
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
  assert_equal ~msg:("cyclic check for "^s) (gs_is_cyclic gs) cyclic

let tests =
  TestList
    [ "Non-parametric"  >:::
      [ "acyclic" >:: (test_cyclic "gs_bilinear_sym" gs_bilinear_sym false)
      ; "acyclic" >:: (test_cyclic "gs_bilinear_asym" gs_bilinear_asym false)
      ; "cyclic " >:: (test_cyclic "gs2" gs2 true) ] ]

let () =
  ignore (check ());
  ignore (run_test_tt_main tests)