(*i*)
open NonParamInput
(*i*)

(*******************************************************************)
(* \hd{Predefined group settings} *)

let gs_bilinear_asym = close_group_setting {
  gs_isos = [{ iso_dom = "1"; iso_codom = "2"}];
  gs_emaps = [{ em_dom = ["1";"2"]; em_codom = "1:2"}];
}

let gs_bilinear_sym = close_group_setting {
  gs_isos = [];
  gs_emaps = [{ em_dom = ["1";"1"]; em_codom = "2"}];
}
