(* This file is distributed under the MIT License (see LICENSE). *)

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
let vi = var_exp "V" (-1)
let wi = var_exp "W" (-1)

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
  let cS_vr = gen () in
  let cS_vw = gen () in
  let cS_wr = gen () in
  let cS_wm = gen () in
  let cS_ww = gen () in
  let cS_rr = gen () in
  let cS_rm = gen () in

  let s_poly =
                       (* e(-,H)        e(-,R)        e(-,M)         e(_,W) *)
  (* e(V,-) *)        (cS_v  * v)   + (cS_vr * v*r) + (cS_vm * v*m) + (cS_vw * v*w)
  (* e(phi(W),-) *)   (* W known *) + (cS_wr * w*r) + (cS_wm * w*m) + (cS_ww * w*w)
  (* e(phi(R),-) *)   (* R known *) + (cS_rr * r*r) + (cS_rm * r*m)   (* dupl.   *)
  (* e(phi(M),-) *)   (* M known *)   (*  dupl.  *)   (* nocomp *)    (* dupl.   *) 
  (* e(G,-)      *)   (* 1 known *)   (*  dupl.  *)   (* dupl.  *)    (* dupl.   *)
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
    ; cS_rm + cS_rr + cS_vr + cS_wr ]  (* R used *)
  in
  let symmetries =
    ([ s_poly ],
     [ [(m,m -@ one)]
     ; [(v,v -@ one)]
     ; [(w,w -@ one)]
     ; [(r,r -@ one)]
     ; [(r,r -@ w)]
     ; [(m,m -@ w)]
     ; [(r,r -@ w -@ m)]
     ; [(r,r -@ w -@ one)]
     ; [(r,r -@ w -@ one -@ m)]
     ; [(m,m -@ w -@ one)]
     ; [(v,v -@ w); (w,w)]  (* linear combinations *)
     ; [(v,v +@ w); (w,w)]  (* linear combinations *)
     ])
  in
  { sps_t           = sps_t;
    choices         = [0; 1];
    vars            = !vars;
    symmetries      = symmetries;
    nonzero_constrs = nonzero_constrs;
    zero_constrs    = [];
    equivsigs       = []
  }

(*******************************************************************)
(* \hd{Spec for V in G1, W in G2 random, R random in G2, and
       verification equation S*R = g(M,R,V,W)} *)

let spec2 () =
  let cS_v   = gen () in
  let cS_vr  = gen () in
  let cS_vm  = gen () in
  let cS_vw  = gen () in
  let cS_w   = gen () in
  let cS_wm  = gen () in
  let cS_ww  = gen () in
  let cS_m   = gen () in
  let cS_1   = gen () in

  let s_poly =
                       (* e(-,H)        e(-,R)           e(-,M)         e(_,W) *)
  (* e(V,-) *)        (cS_v * v)    + (cS_vr * v*r) + (cS_vm * v*m) + (cS_vw * v*w)
  (* e(phi(W),-) *) + (cS_w * w)      (* W known *) + (cS_wm * w*m) + (cS_ww * w*w)
  (* e(phi(R),-) *)   (* 1 known *)   (* R known *)   (* M known *)   (* dupl.   *)
  (* e(phi(M),-) *) + (cS_m * m)      (* dupl.   *)   (* nocomp  *)   (* dupl.   *) 
  (* e(G,-)      *) + (cS_1 * one)    (* dupl.   *)   (* dupl.   *)   (* dupl.   *)
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
  let symmetries =
    ([ s_poly * ri ],
     [ [(m,m -@ one)]
     ; [(v,v -@ one)]
     ; [(w,w -@ one)]
     ; [(m,m -@ w)]
     ; [(m,m -@ w -@ one)]
     ; [(v,v -@ w); (w,w)]  (* linear combinations *)
     ; [(v,v +@ w); (w,w)]  (* linear combinations *)
     ])
  in
  (* R is always used unless S = R*g where g does not contain R *)
  let nonzero_constrs = [ cS_vm + cS_wm ] in (* M used *)
  { sps_t           = sps_t;
    choices         = [0; 1];
    vars            = !vars;
    symmetries      = symmetries; (* []; *) (* V and W in different groups *)
    nonzero_constrs = nonzero_constrs;
    zero_constrs    = [];
    equivsigs       = []
  }

(*******************************************************************)
(* \hd{Spec for V in G1, W in G2 random, T = R + V in G2, and
       verification equation (T - V)*S = g(M,R,V,W)} *)

let spec3 () =
  let cS_v  = gen () in
  let cS_vr = gen () in
  let cS_vm = gen () in
  let cS_vw = gen () in
  let cS_vv = gen () in
  let cS_w  = gen () in
  let cS_wm = gen () in
  let cS_ww = gen () in
  let cS_m  = gen () in
  let cS_1  = gen () in

  (* We overapproximate what can be computed using e(-,T) by allowing for e(-,V). *)
  let s_poly =
                       (* e(-,H)        e(-,R)           e(-,M)         e(_,W)        e(_,V) *)
  (* e(V,-) *)        (cS_v * v)    + (cS_vr * v*r) + (cS_vm * v*m) + (cS_vw * v*w) + (cS_vv * v*v)
  (* e(phi(W),-) *) + (cS_w * w)      (* W known *) + (cS_wm * w*m) + (cS_ww * w*w)   (* dupl.   *)
  (* e(phi(R),-) *)   (* 1 known *)   (* R known *)   (* M known *)   (* dupl    *)   (* dupl.   *)
  (* e(phi(M),-) *) + (cS_m * m)      (* dupl.   *)   (* nocomp  *)   (* dupl.   *)   (* dupl.   *)
  (* e(G,-)      *) + (cS_1 * one)    (* dupl.   *)   (* dupl.   *)   (* dupl.   *)   (* dupl.   *)
  in
  let t = r + v in
  let sps_t =
    { sps_def with
      key_left    = [v];
      key_right   = [w];
      msg_right_n = ["M"];
      sig_right   = [t; s_poly * ri];
      sig_right_n = ["T"; "S"];
      osample     = ["R"]
    }
  in
  let symmetries =
    ([ t; s_poly * ri ],
     [ [(m,m -@ one)]
     ; [(v,v -@ one)]
     ; [(w,w -@ one)]
     ; [(m,m -@ w)]
     ; [(m,m -@ w -@ one)]
     ; [(v,v -@ w); (w,w)]  (* linear combinations *)
     ; [(v,v +@ w); (w,w)]  (* linear combinations *)
     ])
  in
  (* R is nearly always used since S is divided by R *)
  let nonzero_constrs = [ cS_vm + cS_wm + cS_m ] in (* M used *)
  let equivsigs =
    [ [ t; (s_poly * ri) -@ t]
    ; [ t; (s_poly * ri) -@ t -@ one]
    ; [ t; (s_poly * ri) -@ t -@ m]
    ; [ t; (s_poly * ri) -@ t -@ w]
    ; [ t; (s_poly * ri) -@ t -@ m -@ one]
    ; [ t; (s_poly * ri) -@ t -@ m -@ w]
    ; [ t; (s_poly * ri) -@ t -@ one -@ w]
    ; [ t; (s_poly * ri) -@ m ]
    ; [ t; (s_poly * ri) -@ m -@ one]
    ; [ t; (s_poly * ri) -@ m -@ w]
    ; [ t; (s_poly * ri) -@ m -@ w -@ one]
    ; [ t; (s_poly * ri) -@ one]
    ; [ t; (s_poly * ri) -@ one -@ w]
    ; [ t; (s_poly * ri) -@ w]
    ] 
  in
  { sps_t           = sps_t;
    choices         = [0; 1];
    vars            = !vars;
    symmetries      = symmetries;
    nonzero_constrs = nonzero_constrs;
    zero_constrs    = [];
    equivsigs       = equivsigs;
  }

(*******************************************************************)
(* \hd{Spec for V in G1, W in G2 random, T = R + V in G2, and
       verification equation (T - V)*S = g(M,R,V,W)} *)

let spec4 () =
  let cS_rr = gen () in
  let cS_r  = gen () in
  let cS_rm = gen () in
  let cS_w  = gen () in
  let cS_wr = gen () in
  let cS_wm = gen () in
  let cS_ww = gen () in
  let cS_m  = gen () in
  let cS_1  = gen () in

  let s_poly =
                       (* e(-,H)        e(-,R)           e(-,M)         e(_,W)   *)
  (* e(V,-) *)        (* 1 known *)   (* R known *)   (* M known *)   (* W known *) 
  (* e(phi(W),-) *)   (cS_w * w)    + (cS_wr * w*r) + (cS_wm * w*m) + (cS_ww * w*w) 
  (* e(phi(R),-) *) + (cS_r * r)    + (cS_rr * r*r) + (cS_rm * r*m)   (* dupl    *) 
  (* e(phi(M),-) *) + (cS_m * m)      (* dupl.   *)   (* nocomp  *)   (* dupl.   *) 
  (* e(G,-)      *) + (cS_1 * one)    (* dupl.   *)   (* dupl.   *)   (* dupl.   *) 
  in
  let sps_t =
    { sps_def with
      key_left    = [v];
      key_right   = [w];
      msg_right_n = ["M"];
      sig_right   = [r; s_poly * vi];
      sig_right_n = ["T"; "S"];
      osample     = ["R"]
    }
  in
  let symmetries =
    ([ r; s_poly * ri ],
     [ [(m,m -@ one)]
     ; [(v,v -@ one)]
     ; [(w,w -@ one)]
     ; [(m,m -@ w)]
     ; [(m,m -@ w -@ one)]
     ; [(v,v -@ w); (w,w)]  (* linear combinations *)
     ; [(v,v +@ w); (w,w)]  (* linear combinations *)
     ])
  in
  (* R is nearly always used since S is divided by R *)
  let nonzero_constrs = [ cS_rm + cS_wm + cS_m ] in (* M used *)
  let equivsigs =
    [ [ r; (s_poly * ri) -@ r]
    ; [ r; (s_poly * ri) -@ r -@ one]
    ; [ r; (s_poly * ri) -@ r -@ m]
    ; [ r; (s_poly * ri) -@ r -@ w]
    ; [ r; (s_poly * ri) -@ r -@ m -@ one]
    ; [ r; (s_poly * ri) -@ r -@ m -@ w]
    ; [ r; (s_poly * ri) -@ r -@ one -@ w]
    ; [ r; (s_poly * ri) -@ m ]
    ; [ r; (s_poly * ri) -@ m -@ one]
    ; [ r; (s_poly * ri) -@ m -@ w]
    ; [ r; (s_poly * ri) -@ m -@ w -@ one]
    ; [ r; (s_poly * ri) -@ one]
    ; [ r; (s_poly * ri) -@ one -@ w]
    ; [ r; (s_poly * ri) -@ w]
    ] 
  in
  { sps_t           = sps_t;
    choices         = [0; 1];
    vars            = !vars;
    symmetries      = symmetries;
    nonzero_constrs = nonzero_constrs;
    zero_constrs    = [];
    equivsigs       = equivsigs;
  }

(*******************************************************************)
(* \hd{Spec for V in G1, W in G2 random, T = R + V in G2, and
       verification equation (T - V)*S = g(M,R,V,W)} *)

let spec5 () =
  let cS_v  = gen () in
  let cS_vr = gen () in
  let cS_vm = gen () in
  let cS_vw = gen () in
  let cS_rr = gen () in
  let cS_r  = gen () in
  let cS_rm = gen () in
  let cS_m  = gen () in
  let cS_1  = gen () in

  let s_poly =
                       (* e(-,H)        e(-,R)           e(-,M)         e(_,W)   *)
  (* e(V,-) *)        (cS_v * v)    + (cS_vr * v*r) + (cS_vm * v*m) + (cS_vw * v*w)
  (* e(phi(W),-) *)   (* 1 known *)   (* R known *)   (* M known *)   (* W known *)
  (* e(phi(R),-) *) + (cS_r * r)    + (cS_rr * r*r) + (cS_rm * r*m)   (* dupl    *) 
  (* e(phi(M),-) *) + (cS_m * m)      (* dupl.   *)   (* nocomp  *)   (* dupl.   *) 
  (* e(G,-)      *) + (cS_1 * one)    (* dupl.   *)   (* dupl.   *)   (* dupl.   *) 
  in
  let sps_t =
    { sps_def with
      key_left    = [v];
      key_right   = [w];
      msg_right_n = ["M"];
      sig_right   = [r; s_poly * wi];
      sig_right_n = ["T"; "S"];
      osample     = ["R"]
    }
  in
  let symmetries =
    ([ r; s_poly * ri ],
     [ [(m,m -@ one)]
     ; [(v,v -@ one)]
     ; [(w,w -@ one)]
     ; [(m,m -@ w)]
     ; [(m,m -@ w -@ one)]
     ; [(v,v -@ w); (w,w)]  (* linear combinations *)
     ; [(v,v +@ w); (w,w)]  (* linear combinations *)
     ])
  in
  (* R is nearly always used since S is divided by R *)
  let nonzero_constrs = [ cS_rm + cS_vm + cS_m ] in (* M used *)
  let equivsigs =
    [ [ r; (s_poly * ri) -@ r]
    ; [ r; (s_poly * ri) -@ r -@ one]
    ; [ r; (s_poly * ri) -@ r -@ m]
    ; [ r; (s_poly * ri) -@ r -@ w]
    ; [ r; (s_poly * ri) -@ r -@ m -@ one]
    ; [ r; (s_poly * ri) -@ r -@ m -@ w]
    ; [ r; (s_poly * ri) -@ r -@ one -@ w]
    ; [ r; (s_poly * ri) -@ m ]
    ; [ r; (s_poly * ri) -@ m -@ one]
    ; [ r; (s_poly * ri) -@ m -@ w]
    ; [ r; (s_poly * ri) -@ m -@ w -@ one]
    ; [ r; (s_poly * ri) -@ one]
    ; [ r; (s_poly * ri) -@ one -@ w]
    ; [ r; (s_poly * ri) -@ w]
    ] 
  in
  { sps_t           = sps_t;
    choices         = [0; 1];
    vars            = !vars;
    symmetries      = symmetries;
    nonzero_constrs = nonzero_constrs;
    zero_constrs    = [];
    equivsigs       = equivsigs;
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
