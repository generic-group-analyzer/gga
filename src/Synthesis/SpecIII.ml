(*i*)
open Util
open LStringPoly
open Synthesis

open SpecDefs
open SP

(*i*)

let spec = 

  let v = var "V" in
  let w = var "W" in
  let r = var "R" in
  let m = var "M" in

  let rinv = var_exp "R" (-1) in 

  let (vars,gen) = var_gen () in
  let cS_v     = gen () in
  let cS_w     = gen () in
  let cS_vm    = gen () in
  let cS_wm    = gen () in
  let cS_rm    = gen () in
  let cS_rw    = gen () in
  let cS_rv    = gen () in
  let cS_rr    = gen () in
  let cR2_r    = gen () in
  let cR2_rinv = gen () in

  let s_poly =
    L.map mult_var
      [ (cS_v, v); (cS_w,w); (cS_vm, v *@ m); (cS_wm, w *@ m); (cS_rm, r *@ m)
      ; (cS_rr, r *@ r); (cS_rv, r *@ v); (cS_rw, r *@ w) ]
  in
  
  let r2_poly = L.map mult_var [ (cR2_r,r); (cR2_rinv,rinv) ] in
  let sps_t =
    { key_left    = [v; w];
      key_right   = [];
      msg_left_n  = [];
      msg_right_n = ["M"];
      sig_left    = [r];
      sig_left_n  = ["R1"];
      sig_right   = [lmult r2_poly; lmult s_poly ];
      sig_right_n = ["R2"; "S"];
      setting     = TY3;
      osample     = ["R"]
    }
  in

  let nonzero_constrs =
    [ [cS_vm;cS_wm;cS_rm]        (* m used *)
    (* ; [cS_v;cS_vm;cS_rv]         (* v used *)
    ; [cS_w;cS_wm;cS_rw]         (* w used *)
    ; [cS_rm;cS_rr;cS_rv;cS_rw]  (* r used *) *)
    ; [cR2_r;cR2_rinv]           (* one of R or R^-1 for R1 nonzero *)
    ]
  in
  let zero_constrs = 
    [ [cR2_r; cR2_rinv ] ] (* one of R or R^-1 for R1 zero *)
  in
  let symmetry = [ (cS_v,cS_w); (cS_vm,cS_wm) ] in
  { sps_t = sps_t;
    vars = !vars;
    symmetry = symmetry;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = zero_constrs
  }
