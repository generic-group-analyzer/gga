(*i*)
open Util
open LStringPoly
open Synthesis

open SpecDefs
open SP
(*i*)

(* spec for verification equation S = f(R,V,W,M) *)
let spec1 = 

  let v = var "V" in
  let w = var "W" in
  let r = var "R" in
  let m = var "M" in

  let (vars,gen) = var_gen () in
  let cS_v  = gen () in
  let cS_w  = gen () in
  let cS_vm = gen () in
  let cS_wm = gen () in
  let cS_rm = gen () in
  let cS_rw = gen () in
  let cS_rv = gen () in
  let cS_rr = gen () in

  let s_poly =
    L.map mult_var
      [ (cS_v, v); (cS_w, w)
      ; (cS_vm, v *@ m); (cS_wm, w *@ m); (cS_rm, r *@ m)
      ; (cS_rr, r *@ r); (cS_rv, r *@ v); (cS_rw, r *@ w) ]
  in
  let sps_t =
    { key_left    = [v; w];
      key_right   = [];
      msg_left_n  = [];
      msg_right_n = ["M"];
      sig_left    = [];
      sig_left_n  = [];
      sig_right   = [r; ladd s_poly ];
      sig_right_n = ["R"; "S"];
      setting     = TY2;
      osample     = ["R"]
    }
  in

  let nonzero_constrs =
    [ [cS_vm;cS_wm;cS_rm]        (* m used *)
    (* ; [cS_v;cS_vm;cS_rv]      (* v used *)
       ; [cS_w;cS_wm;cS_rw]      (* w used *) *)
    ; [cS_rm;cS_rr;cS_rv;cS_rw]  (* r used *)
    ]
  in
  let zero_constrs = [] in
  let symmetry = [ (cS_v,cS_w); (cS_vm,cS_wm) ] in
  { sps_t = sps_t;
    vars = !vars;
    symmetry = symmetry;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = zero_constrs
  }

(* spec for verification equation S*g(R,V,W) = f(R,V,W,M) *)
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
  let cR_rand = gen () in
  let cR_plus_v = gen () in
  let cR_plus_w = gen () in
  let cR_plus_v_w = gen () in

  let s_poly =
    L.map mult_var
      [ (cS_v, v); (cS_w, w); (cS_m, m); (cS_1, from_int 1)
      ; (cS_vm, v *@ m); (cS_wm, w *@ m); (cS_rm, r *@ m)
      ; (cS_rv, r *@ v); (cS_rw, r *@ w); (cS_r, r) ]
  in
  let t_poly =
    L.map mult_var
      [ (cR_rand, r)
      ; (cR_plus_v, r +@ v)
      ; (cR_plus_w, r +@ w)
      ; (cR_plus_v_w, r +@ v +@ w)
      ]
  in
  let sps_t =
    { key_left    = [v; w];
      key_right   = [];
      msg_left_n  = [];
      msg_right_n = ["M"];
      sig_left    = [];
      sig_left_n  = [];
      sig_right   = [ladd t_poly; ladd s_poly *@ ri ];
      sig_right_n = ["T"; "S"];
      setting     = TY2;
      osample     = ["R"]
    }
  in

  (* r always used since s = ... / r *)
  let nonzero_constrs =
    [ [cS_vm;cS_wm;cS_rm;cS_m]                      (* m used *)
    (* ; [cS_v;cS_vm;cS_rv;cR_plus_v;cR_plus_v_w]   (* v used *)
       ; [cS_w;cS_wm;cS_rw;cR_plus_w;cR_plus_v_w]   (* w used *) *)
    ; [cR_rand;cR_plus_v;cR_plus_w;cR_plus_v_w]  (* one of the choices for R *)
    ]
  in
  (* not more than one of the choices for R *)
  let zero_constrs =
    [ [cR_rand;cR_plus_v]
    ; [cR_rand;cR_plus_w]
    ; [cR_rand;cR_plus_v_w]
    ; [cR_plus_v;cR_plus_w]
    ; [cR_plus_v;cR_plus_v_w]
    ; [cR_plus_w;cR_plus_v_w]
    ]
  in
  let symmetry = [ (cS_v,cS_w); (cS_vm,cS_wm) ] in
  { sps_t = sps_t;
    vars = !vars;
    symmetry = symmetry;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = zero_constrs
  }

(* spec mixed key, verification equation S = f(R,V,W,M) *)
let spec3 = 
  let v = var "V" in
  let w = var "W" in
  let r = var "R" in
  let m = var "M" in

  let (vars,gen) = var_gen () in
  let cS_v   = gen () in
  let cS_w   = gen () in
  let cS_m   = gen () in
  let cS_vm  = gen () in
  let cS_wm  = gen () in
  let cS_rw  = gen () in
  let cS_ww  = gen () in
  let cS_rv  = gen () in
  let cS_rr  = gen () in


  let s_poly =
    L.map mult_var
      [ (cS_v, v); (cS_w, w); (cS_m, m); (cS_rr, r *@ r)
      ; (cS_ww, w *@ w)
      ; (cS_vm, v *@ m); (cS_wm, w *@ m)
      ; (cS_rv, r *@ v); (cS_rw, r *@ w) ]
  in
  let t_poly = r in
  let sps_t =
    { key_left    = [v];
      key_right   = [w];
      msg_left_n  = [];
      msg_right_n = ["M"];
      sig_left    = [];
      sig_left_n  = [];
      sig_right   = [t_poly; ladd s_poly ];
      sig_right_n = ["T"; "S"];
      setting     = TY2;
      osample     = ["R"]
    }
  in

  (* r always used since s = / r *)
  let nonzero_constrs =
    [ [cS_vm;cS_wm;cS_m]                               (* m used *)
    (* ; [cS_v;cS_vm;cS_rv;cR_plus_v;cR_plus_v_w]         (* v used *)
    ; [cS_w;cS_wm;cS_rw;cS_ww;cR_plus_w;cR_plus_v_w]   (* w used *) *)
    ]
  in
  (* not more than one of the choices for R *)
  let zero_constrs = [] in
  let symmetry = [ (cS_v,cS_w); (cS_vm,cS_wm) ] in
  { sps_t = sps_t;
    vars = !vars;
    symmetry = symmetry;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = zero_constrs
  }

(* spec mixed key: S*g(R,V,W) = f(R,V,W,M) *)
let spec4 = 
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
  let cS_rw  = gen () in
  let cS_ww  = gen () in
  let cS_rv  = gen () in
  let cS_1   = gen () in

  (* choose R *)
  let cR_rand = gen () in
  let cR_plus_v = gen () in
  let cR_plus_w = gen () in
  let cR_plus_v_w = gen () in

  let s_poly =
    L.map mult_var
      [ (cS_v, v); (cS_w, w); (cS_m, m); (cS_1, from_int 1)
      ; (cS_ww, w *@ w)
      ; (cS_vm, v *@ m); (cS_wm, w *@ m)
      ; (cS_rv, r *@ v); (cS_rw, r *@ w) ]
  in
  let t_poly =
    L.map mult_var
      [ (cR_rand, r)
      ; (cR_plus_v, r +@ v)
      ; (cR_plus_w, r +@ w)
      ; (cR_plus_v_w, r +@ v +@ w)
      ]
  in
  let sps_t =
    { key_left    = [v];
      key_right   = [w];
      msg_left_n  = [];
      msg_right_n = ["M"];
      sig_left    = [];
      sig_left_n  = [];
      sig_right   = [ladd t_poly; (ladd s_poly) *@ ri ];
      sig_right_n = ["T"; "S"];
      setting     = TY2;
      osample     = ["R"]
    }
  in

  (* r always used since s = / r *)
  let nonzero_constrs =
    [ [cS_vm;cS_wm;cS_m]                               (* m used *)
    (* ; [cS_v;cS_vm;cS_rv;cR_plus_v;cR_plus_v_w]         (* v used *)
    ; [cS_w;cS_wm;cS_rw;cS_ww;cR_plus_w;cR_plus_v_w]   (* w used *) *)
    ; [cR_rand;cR_plus_v;cR_plus_w;cR_plus_v_w]        (* one of the choices for R *)
    ]
  in
  (* not more than one of the choices for R *)
  let zero_constrs =
    [ [cR_rand;cR_plus_v]
    ; [cR_rand;cR_plus_w]
    ; [cR_rand;cR_plus_v_w]
    ; [cR_plus_v;cR_plus_w]
    ; [cR_plus_v;cR_plus_v_w]
    ; [cR_plus_w;cR_plus_v_w]
    ]
  in
  let symmetry = [ (cS_v,cS_w); (cS_vm,cS_wm) ] in
  { sps_t = sps_t;
    vars = !vars;
    symmetry = symmetry;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = zero_constrs
  }
