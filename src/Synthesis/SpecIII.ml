(*i*)
open Util
open LStringPoly
open Synthesis

open SpecDefs
open SP

(*i*)

(* Type III setting, both keys in G1, no Laurent polynomials *)
let spec1 = 

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
      [ (cS_v, v); (cS_w, w); (cS_vm, v *@ m); (cS_wm, w *@ m); (cS_rm, r *@ m)
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
      sig_right   = [ladd r2_poly; ladd s_poly ];
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
    [ [cR2_r; cR2_rinv ] ] (* one of R or R^-1 for R2 zero *)
  in
  let symmetry = [ (cS_v,cS_w); (cS_vm,cS_wm) ] in
  { sps_t = sps_t;
    vars = !vars;
    symmetry = symmetry;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = zero_constrs
  }

(* Type III: verification equation S*R = f(R,V,W,M), T=g(R,V,W) *)
let spec2 = 
  let v = var "V" in
  let w = var "W" in
  let r = var "R" in
  let m = var "M" in
  let ri = var_exp "R" (-1) in

  let (vars,gen) = var_gen () in
  let cS_v   = gen () in
  let cS_w   = gen () in
  let cS_m   = gen () in
  let cS_vm  = gen () in
  let cS_wm  = gen () in
  let cS_rm  = gen () in
  let cS_rw  = gen () in
  let cS_rv  = gen () in
  let cS_r   = gen () in
  let cS_1   = gen () in

  (* choose R *)
  let cT1_rand = gen () in
  let cT1_plus_v = gen () in
  let cT1_plus_w = gen () in
  let cT1_plus_v_w = gen () in

  let cT2_copy = gen () in
  let cT2_inv  = gen () in

  let s_poly =
    L.map mult_var
      [ (cS_v, v); (cS_w, w); (cS_m, m); (cS_1, from_int 1)
      ; (cS_vm, v *@ m); (cS_wm, w *@ m); (cS_rm, r *@ m)
      ; (cS_rv, r *@ v); (cS_rw, r *@ w); (cS_r, r) ]
  in
  let t1_poly =
    L.map mult_var
      [ (cT1_rand, r)
      ; (cT1_plus_v, r +@ v)
      ; (cT1_plus_w, r +@ w)
      ; (cT1_plus_v_w, r +@ v +@ w)
      ]
  in
  let t2_poly =
    L.map mult_var
      [ (cT2_copy, r)
      ; (cT2_inv, ri)
      ]
  in
  let sps_t =
    { key_left    = [v; w];
      key_right   = [];
      msg_left_n  = [];
      msg_right_n = ["M"];
      sig_left    = [ladd t1_poly];
      sig_left_n  = ["T1"];
      sig_right   = [ladd t2_poly; ladd s_poly *@ ri ];
      sig_right_n = ["T2"; "S"];
      setting     = TY3;
      osample     = ["R"]
    }
  in

  (* r always used since s = ... / r *)
  let nonzero_constrs =
    [ [cS_vm;cS_wm;cS_rm;cS_m]                      (* m used *)
    ; [cT1_rand;cT1_plus_v;cT1_plus_w;cT1_plus_v_w] (* one of the choices for T1 *)
    ; [cT2_copy;cT2_inv]                            (* one of the choices for T2 *)
    (* ; [cS_v;cS_vm;cS_rv;cR_plus_v;cR_plus_v_w]   (* v used *)
       ; [cS_w;cS_wm;cS_rw;cR_plus_w;cR_plus_v_w]   (* w used *) *)
    ]
  in
  (* not more than one of the choices for R *)
  let zero_constrs =
    [ [cT1_rand;cT1_plus_v]
    ; [cT1_rand;cT1_plus_w]
    ; [cT1_rand;cT1_plus_v_w]
    ; [cT1_plus_v;cT1_plus_w]
    ; [cT1_plus_v;cT1_plus_v_w]
    ; [cT1_plus_w;cT1_plus_v_w]
    ; [cT2_copy;cT2_inv]
    ]
  in
  let symmetry = [ (cS_v,cS_w); (cS_vm,cS_wm) ] in
  { sps_t = sps_t;
    vars = !vars;
    symmetry = symmetry;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = zero_constrs
  }
