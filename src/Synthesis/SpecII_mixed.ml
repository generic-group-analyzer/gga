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
(* \hd{Spec for both keys V in G1, W in G2 random, R random in G2, and
       verification equation S = g(M,R,V,W)} *)

let spec1 () =
  let cS_v  = gen () in
  let cS_vm = gen () in
  let cS_wm = gen () in
  let cS_rm = gen () in
  let cS_rw = gen () in
  let cS_rv = gen () in
  let cS_rr = gen () in
  let cS_ww = gen () in
  let cS_wv = gen () in

  let s_poly =
      (cS_v  * v)
    + (cS_vm * v*m) + (cS_wm * w*m) + (cS_rm * r*m)
    + (cS_rr * r*r) + (cS_rv * r*v) + (cS_rw * r*w)
    + (cS_ww * w*w) + (cS_wv * w*v)
  in
  let sps_t =
    { sps_def with
      key_left    = [v];
      key_right   = [w];
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
  { sps_t           = sps_t;
    choices         = [0; 1];
    vars            = !vars;
    symmetries      = []; (* V and W in different groups *)
    nonzero_constrs = nonzero_constrs;
    zero_constrs    = []
  }

(*******************************************************************)
(* \hd{Spec for V in G1, W in G2 random, R random in G2, and
       verification equation S*R = g(M,R,V,W)} *)

let spec2 () =
  let cS_v   = gen () in
  let cS_w   = gen () in
  let cS_vm  = gen () in
  let cS_wm  = gen () in
  let cS_rv  = gen () in
  let cS_rrv = gen () in
  let cS_rr  = gen () in
  let cS_ww  = gen () in
  let cS_wv  = gen () in
  let cS_1   = gen () in

  let s_poly =
      (cS_v  * v)   + (cS_w  * w)
    + (cS_vm * v*m) + (cS_wm * w*m)
    + (cS_rr * r*r) + (cS_rv * r*v)
    + (cS_ww * w*w) + (cS_wv * w*v)
    + (cS_1  * SP.from_int 1)
  in
  let sps_t =
    { sps_def with
      key_left    = [v];
      key_right   = [w];
      msg_right_n = ["M"];
      sig_right   = [r; s_poly * ri];
      sig_right_n = ["R"; "S"];
      osample     = ["R"]
    }
  in
  (* R is always used unless S = R*g where g does not contain R *)
  let nonzero_constrs = [ cS_vm + cS_wm ] in (* M used *)
  { sps_t           = sps_t;
    choices         = [0; 1];
    vars            = !vars;
    symmetries      = []; (* V and W in different groups *)
    nonzero_constrs = nonzero_constrs;
    zero_constrs    = []
  }

(*******************************************************************)
(* \hd{Spec for V in G1, W in G2 random, T = R + V in G2, and
       verification equation (T - V)*S = g(M,R,V,W)} *)

let spec3 () =
  let cS_v  = gen () in
  let cS_w  = gen () in
  let cS_vm = gen () in
  let cS_wm = gen () in
  let cS_rv = gen () in
  let cS_rr = gen () in
  let cS_ww = gen () in
  let cS_wv = gen () in
  let cS_1  = gen () in

  let s_poly =
      (cS_v  * v)   + (cS_w  * w)
    + (cS_vm * v*m) + (cS_wm * w*m)
    + (cS_rr * r*r) + (cS_rv * r*v)
    + (cS_ww * w*w) + (cS_wv * w*v)
    + (cS_1  * SP.from_int 1)
  in
  let sps_t =
    { sps_def with
      key_left    = [v];
      key_right   = [w];
      msg_right_n = ["M"];
      sig_right   = [r + v; s_poly * ri];
      sig_right_n = ["T"; "S"];
      osample     = ["R"]
    }
  in
  (* R is nearly always used since S is divided by R *)
  let nonzero_constrs = [ cS_vm + cS_wm ] in (* M used *)
  { sps_t           = sps_t;
    choices         = [0; 1];
    vars            = !vars;
    symmetries      = []; (* V and W in different groups *)
    nonzero_constrs = nonzero_constrs;
    zero_constrs    = []
  }

(* Note that T = R + W can be reduced to T = R since W is
   given in G2. For T = R + W^2, we already require a multiplication
   to obtain R and then we cannot perform a multiplication with S
   anymore.

   So the below specs do not have verification equations unless they are
   trivially attackable.
   
(*******************************************************************)
(* \hd{Spec for V in G1, W in G2 random, T = R + W^2 in G2, and
       verification equation S*(T - W^2) = g(M,R,V,W).} *)
  
let spec4 () =
  let cS_v  = gen () in
  let cS_w  = gen () in
  let cS_vm = gen () in
  let cS_wm = gen () in
  let cS_rm = gen () in
  let cS_rw = gen () in
  let cS_rv = gen () in
  let cS_rr = gen () in
  let cS_ww = gen () in
  let cS_wv = gen () in

  let s_poly =
      (cS_v  * v)   + (cS_w  * w)
    + (cS_vm * v*m) + (cS_wm * w*m) + (cS_rm * r*m)
    + (cS_rr * r*r) + (cS_rv * r*v) + (cS_rw * r*w)
    + (cS_ww * w*w) + (cS_wv * w*v)
  in
  let sps_t =
    { sps_def with
      key_left    = [v];
      key_right   = [w];
      msg_right_n = ["M"];
      sig_right   = [r + w*w; s_poly * ri];
      sig_right_n = ["T"; "S"];
      osample     = ["R"]
    }
  in
  (* R is always used unless S = R*g where g does not contain R *)
  let nonzero_constrs =
    [ cS_vm + cS_wm + cS_rm ] (* M used *)
  in
  { sps_t           = sps_t;
    choices         = [0; 1];
    vars            = !vars;
    symmetries      = []; (* V and W in different groups *)
    nonzero_constrs = nonzero_constrs;
    zero_constrs    = []
  }

(*******************************************************************)
(* \hd{Spec for V in G1, W in G2 random, T = R + V + W^2 in G2, and
       verification equation S*(T - W^2 - V) = g(M,R,V,W)} *)

let spec5 () =
  let cS_v  = gen () in
  let cS_w  = gen () in
  let cS_vm = gen () in
  let cS_wm = gen () in
  let cS_rm = gen () in
  let cS_rw = gen () in
  let cS_rv = gen () in
  let cS_rr = gen () in
  let cS_ww = gen () in
  let cS_wv = gen () in

  let s_poly =
      (cS_v  * v)   + (cS_w  * w)
    + (cS_vm * v*m) + (cS_wm * w*m) + (cS_rm * r*m)
    + (cS_rr * r*r) + (cS_rv * r*v) + (cS_rw * r*w)
    + (cS_ww * w*w) + (cS_wv * w*v)
  in
  let sps_t =
    { sps_def with
      key_left    = [v];
      key_right   = [w];
      msg_right_n = ["M"];
      sig_right   = [r + v + w*w; s_poly * ri];
      sig_right_n = ["T"; "S"];
      osample     = ["R"]
    }
  in
  (* R is always used unless S = R*g where g does not contain R *)
  let nonzero_constrs =
    [ cS_vm + cS_wm + cS_rm ] (* M used *)
  in
  { sps_t           = sps_t;
    choices         = [0; 1];
    vars            = !vars;
    symmetries      = []; (* V and W in different groups *)
    nonzero_constrs = nonzero_constrs;
    zero_constrs    = []
  }

*)
