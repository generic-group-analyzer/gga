(*i*)
open LStringPoly
(* open Synthesis *)

open SP

(*i*)

let v = var "V"
let w = var "W"
let r = var "R"
let m = var "M"
let ri = var_exp "R" (-1)


(* Type III setting, both keys in G1, no Laurent polynomials *)
let spec1 = SpecII.spec1
(*

  let (vars,gen) = var_gen () in
  let cS_v   = gen () in
  let cS_w   = gen () in
  let cS_vm  = gen () in
  let cS_wm  = gen () in
  let cS_rm  = gen () in
  let cS_rw  = gen () in
  let cS_rv  = gen () in
  let cS_rr  = gen () in
  let cR2_r  = gen () in
  let cR2_ri = gen () in

  let s_poly =
    L.map mult_var
      [ (cS_v, v); (cS_w, w); (cS_vm, v *@ m); (cS_wm, w *@ m); (cS_rm, r *@ m)
      ; (cS_rr, r *@ r); (cS_rv, r *@ v); (cS_rw, r *@ w) ]
  in
  
  let r2_poly = L.map mult_var [ (cR2_r,r); (cR2_ri,ri) ] in
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
    [ [cS_vm;cS_wm;cS_rm]           (* m used *)
    (* ; [cS_v;cS_vm;cS_rv]         (* v used *)
       ; [cS_w;cS_wm;cS_rw]         (* w used *)
       ; [cS_rm;cS_rr;cS_rv;cS_rw]  (* r used *) *)
    ; [cR2_r;cR2_ri]           (* one of R or R^-1 for R1 nonzero *)
    ]
  in
  let zero_constrs = 
    [ [cR2_r; cR2_ri] ] (* one of R or R^-1 for R2 zero *)
  in
  let symmetry = [ (cS_v,cS_w); (cS_vm,cS_wm) ] in
  { sps_t = sps_t;
    vars = !vars;
    symmetry = symmetry;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = zero_constrs
  }
*)

(* Type III: verification equation S*R = f(R,V,W,M), T=g(R,V,W) *)
let spec2 = spec1
(*
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
  let sps_t =
    { key_left    = [v; w];
      key_right   = [];
      msg_left_n  = [];
      msg_right_n = ["M"];
      sig_left    = [ladd t1_poly];
      sig_left_n  = ["T1"];
      sig_right   = [ladd t1_poly; ladd s_poly *@ ri ];
      sig_right_n = ["T2"; "S"];
      setting     = TY3;
      osample     = ["R"]
    }
  in

  (* r always used since s = ... / r *)
  let nonzero_constrs =
    [ [cS_vm;cS_wm;cS_rm;cS_m]                      (* m used *)
    ; [cT1_rand;cT1_plus_v;cT1_plus_w;cT1_plus_v_w] (* one of the choices for T1 *)
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
    ]
  in
  let symmetry = [ (cS_v,cS_w); (cS_vm,cS_wm) ] in
  { sps_t = sps_t;
    vars = !vars;
    symmetry = symmetry;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = zero_constrs
  }
*)

(* Type III: verification equation S*R = f(R,V,W,M), T=g(R,V,W) *)
let spec3 = spec1
(*
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

  let s_poly =
    L.map mult_var
      [ (cS_v, v); (cS_w, w); (cS_m, m); (cS_1, from_int 1)
      ; (cS_vm, v *@ m); (cS_wm, w *@ m); (cS_rm, r *@ m)
      ; (cS_rv, r *@ v); (cS_rw, r *@ w); (cS_r, r) ]
  in
  let sps_t =
    { key_left    = [v; w];
      key_right   = [];
      msg_left_n  = [];
      msg_right_n = ["M"];
      sig_left    = [r];
      sig_left_n  = ["T1"];
      sig_right   = [ri; ladd s_poly *@ ri ];
      sig_right_n = ["T2"; "S"];
      setting     = TY3;
      osample     = ["R"]
    }
  in

  (* r always used since s = ... / r *)
  let nonzero_constrs =
    [ [cS_vm;cS_wm;cS_rm;cS_m]                      (* m used *)
    (* ; [cS_v;cS_vm;cS_rv;cR_plus_v;cR_plus_v_w]   (* v used *)
       ; [cS_w;cS_wm;cS_rw;cR_plus_w;cR_plus_v_w]   (* w used *) *)
    ]
  in
  (* not more than one of the choices for R *)
  let zero_constrs =
    [ ]
  in
  let symmetry = [ (cS_v,cS_w); (cS_vm,cS_wm) ] in
  { sps_t = sps_t;
    vars = !vars;
    symmetry = symmetry;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = zero_constrs
  }
*)


(* Type III: verification equation S*R = f(R,V,W,M), T=g(R,V,W). mixed keys *)
let spec4 = spec1
(*
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
  let sps_t =
    { key_left    = [v];
      key_right   = [w];
      msg_left_n  = [];
      msg_right_n = ["M"];
      sig_left    = [ladd t1_poly];
      sig_left_n  = ["T1"];
      sig_right   = [ladd t1_poly; ladd s_poly *@ ri ];
      sig_right_n = ["T2"; "S"];
      setting     = TY3;
      osample     = ["R"]
    }
  in

  (* r always used since s = ... / r *)
  let nonzero_constrs =
    [ [cS_vm;cS_wm;cS_rm;cS_m]                      (* m used *)
    ; [cT1_rand;cT1_plus_v;cT1_plus_w;cT1_plus_v_w] (* one of the choices for T1 *)
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
    ]
  in
  let symmetry = [ (cS_v,cS_w); (cS_vm,cS_wm) ] in
  { sps_t = sps_t;
    vars = !vars;
    symmetry = symmetry;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = zero_constrs
  }
*)