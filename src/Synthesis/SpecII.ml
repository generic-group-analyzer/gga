(*i*)
open LStringPoly
open Synthesis

open SP
(*i*)

(*******************************************************************)
(* \hd{Common definitions} *)

let v = var "V"
let w = var "W"
let r = var "R"
let m = var "M"
let ri = var_exp "R" (-1)

let sps_def =
  { key_left    = [];
    key_right   = [];
    msg_left_n  = [];
    msg_right_n = [];
    sig_left    = [];
    sig_left_n  = [];
    sig_right   = [];
    sig_right_n = [];
    setting     = TY2;
    osample     = []
  }

let (+) = (+@)
let ( * ) = ( *@ )
let (vars,gen) = var_gen ()

(*******************************************************************)
(* \hd{Spec for both keys V,W in G1 and random, R random in G2, and
       verification equation S = g(M,R,V,W)} *)

let spec1 () =
  let cS_v  = gen () in
  let cS_w  = gen () in
  let cS_vm = gen () in
  let cS_wm = gen () in
  let cS_rm = gen () in
  let cS_rw = gen () in
  let cS_rv = gen () in
  let cS_rr = gen () in

  let s_poly =
      (cS_v  * v)   + (cS_w  * w)
    + (cS_vm * v*m) + (cS_wm * w*m) + (cS_rm * r*m)
    + (cS_rr * r*r) + (cS_rv * r*v) + (cS_rw * r*w)
  in
  let sps_t =
    { sps_def with
      key_left    = [v; w];
      msg_right_n = ["M"];
      sig_right   = [r; s_poly];
      sig_right_n = ["R"; "S"];
      osample     = ["R"]
    }
  in
  let nonzero_constrs =
    [ cS_vm + cS_wm + cS_rm            (* M used *)
    ; cS_rm + cS_rr + cS_rv + cS_rw ]  (* R used *)
  in
  (* If two vectors coincide after applying one of the given
     permutations, then one of them is redundant *)
  let symmetries = [[ (cS_v,cS_w); (cS_vm,cS_wm) ]] in
  { sps_t           = sps_t;
    choices         = [0; 1];
    vars            = !vars;
    symmetries        = symmetries;
    nonzero_constrs = nonzero_constrs;
    zero_constrs    = []
  }

(*******************************************************************)
(* \hd{Spec for both keys V,W in G1 and random, R random in G2, and
       verification equation S*R = g(M,R,V,W)} *)

let spec2 () =
  let cS_v   = gen () in
  let cS_w   = gen () in
  let cS_m   = gen () in
  let cS_vm  = gen () in
  let cS_wm  = gen () in
  let cS_rw  = gen () in
  let cS_rv  = gen () in
  let cS_1   = gen () in

  let s_poly =
    (cS_v *  v)   + (cS_w * w)    + (cS_m * m) +
    (cS_vm * v*m) + (cS_wm * w*m) +
    (cS_rv * r*v) + (cS_rw * r*w) + (cS_1 * from_int 1)
  in
  let sps_t =
    { sps_def with
      key_left    = [v; w];
      msg_right_n = ["M"];
      sig_right   = [ r; s_poly *@ ri ];
      sig_right_n = ["R"; "S"];
      setting     = TY2;
      osample     = ["R"]
    }
  in
  let nonzero_constrs = [ cS_vm + cS_wm + cS_m ] in (* m used *)
  let symmetries = [[ (cS_v,cS_w); (cS_vm,cS_wm); (cS_rv,cS_rw) ]] in
  { sps_t = sps_t;
    choices = [0;1];
    vars = !vars;
    symmetries = symmetries;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = []
  }

(*******************************************************************)
(* \hd{Spec for both keys V,W in G1 and random, T = R + W in G2, and
       verification equation S*(T - W) = g(M,R,V,W)} *)

let spec3 () =
  let cS_v   = gen () in
  let cS_w   = gen () in
  let cS_m   = gen () in
  let cS_vm  = gen () in
  let cS_wm  = gen () in
  (* In most cases, we cannot compute R*W and R*V since
     we can only extract R from T in G1. But there are still some
     cases where S has a certain shape *)
  let cS_rw  = gen () in
  let cS_rv  = gen () in
  let cS_1   = gen () in

  let s_poly =
    (cS_v *  v)   + (cS_w * w)    + (cS_m * m) +
    (cS_vm * v*m) + (cS_wm * w*m) +
    (cS_rw * r*w) + (cS_rv * r*v) + (cS_1 * from_int 1)
  in
  let sps_t =
    { sps_def with
      key_left    = [v;w];
      msg_right_n = ["M"];
      sig_right   = [ r + w; s_poly * ri ];
      sig_right_n = ["T"; "S"];
      setting     = TY2;
      osample     = ["R"]
    }
  in
  let nonzero_constrs = [ cS_vm + cS_wm + cS_m ] in (* m used *)
  let symmetries = [] in (* W occurs in T, V doesn't *)
  { sps_t = sps_t;
    choices = [0;1];
    vars = !vars;
    symmetries = symmetries;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = []
  }

(*******************************************************************)
(* \hd{Spec for both keys V,W in G1 and random, T = R + V + W in G2, and
       verification equation S*(T - W - V) = g(M,R,V,W)} *)

let spec4 () =
  let cS_v   = gen () in
  let cS_w   = gen () in
  let cS_m   = gen () in
  let cS_vm  = gen () in
  let cS_wm  = gen () in
  let cS_rw  = gen () in
  let cS_rv  = gen () in
  let cS_1   = gen () in

  let s_poly =
    (cS_v *  v)   + (cS_w * w)    + 
    (cS_vm * v*m) + (cS_wm * w*m) + (cS_m * m) +
    (cS_rv * r*v) + (cS_rw * r*w) + (cS_1 * from_int 1)
  in
  let sps_t =
    { sps_def with
      key_left    = [v; w];
      msg_right_n = ["M"];
      sig_right   = [ r + w + v; s_poly *@ ri ];
      sig_right_n = ["T"; "S"];
      setting     = TY2;
      osample     = ["R"]
    }
  in
  let nonzero_constrs = [ cS_vm + cS_wm + cS_m ] in (* m used *)
  (* the occurences of V and W in T are always symmetric *)
  let symmetries = [[ (cS_v,cS_w); (cS_vm,cS_wm); (cS_rv,cS_rw) ]] in
  { sps_t = sps_t;
    choices = [0;1];
    vars = !vars;
    symmetries = symmetries;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = []
  }
