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
let wi = var_exp "W" (-1)
let one = SP.from_int 1

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
       verification equation S = g(V,W,R,M)} *)

let spec1 () =
  let cS_v  = gen () in
  let cS_w  = gen () in
  let cS_vm = gen () in
  let cS_wm = gen () in
  let cS_rm = gen () in
  let cS_wr = gen () in
  let cS_vr = gen () in
  let cS_rr = gen () in

  let s_poly =
                       (* e(-,H)        e(-,R)        e(-,M) *)
  (* e(V,-) *)        (cS_v  * v) + (cS_vr * v*r) + (cS_vm * v*m)
  (* e(W,-) *)      + (cS_w  * w) + (cS_wr * w*r) + (cS_wm * w*m)
  (* e(phi(R),-) *) + (* known *)   (cS_rr * r*r) + (cS_rm * r*m)
  (* e(phi(M),-) *)   (* known *)   (*  dupl.  *)   (* nocomp *) 
  (* e(G,-)      *)   (* known *)   (* known   *)   (* known  *)
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
    ; cS_rm + cS_rr + cS_vr + cS_wr ]  (* R used *)
  in
  let zero_constrs = [] in
  (* If two vectors coincide after applying one of the given
     permutations, then one of them is redundant *)

  let symmetries =
    ([ s_poly ],
     [ [(v,w); (w,v)]       (* swap V and W *)
     ; [(m,m -@ one)]       (* message transformation *)
     ; [(v,v -@ one)]       (* v transformation *)
     ; [(w,w -@ one)]       (* w transformation *)
     ; [(v,v -@ w); (w,w)]  (* linear combinations *)
     ; [(v,w -@ v); (w,v)]  (* linear combinations *)

     ; [(v,v); (w,w -@ v)]  (* linear combinations *)
     ; [(v,w); (w,v -@ w)]  (* linear combinations *)

     ; [(v,v +@ w); (w,w)]  (* linear combinations *)
     ; [(v,w +@ v); (w,v)]  (* linear combinations *)

     ; [(v,v); (w,w +@ v)]  (* linear combinations *)
     ; [(v,w); (w,v +@ w)]  (* linear combinations *)
     ])
  in
  { sps_t           = sps_t;
    choices         = [0; 1];
    vars            = !vars;
    symmetries      = symmetries;
    nonzero_constrs = nonzero_constrs;
    zero_constrs    = zero_constrs
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
  let cS_wr  = gen () in
  let cS_vr  = gen () in
  let cS_1   = gen () in

  let s_poly =
                       (* e(-,H)        e(-,R)        e(-,M) *)
  (* e(V,-) *)        (cS_v  * v)   + (cS_vr * v*r) + (cS_vm * v*m)
  (* e(W,-) *)      + (cS_w  * w)   + (cS_wr * w*r) + (cS_wm * w*m)
  (* e(phi(R),-) *)   (* 1 known *)   (* r known *)   (* m known *)
  (* e(phi(M),-) *) + (cS_m * m)      (* m known *)   (* nocomp *) 
  (* e(G,-)      *) + (cS_1 * one)    (* 1 known *)   (* dup    *)
  in
  let sps_t =
    { sps_def with
      key_left    = [v; w];
      msg_right_n = ["M"];
      sig_right   = [ r; s_poly * ri ];
      sig_right_n = ["R"; "S"];
      setting     = TY2;
      osample     = ["R"]
    }
  in
  let nonzero_constrs = [ cS_vm + cS_wm + cS_m ] in (* m used *)
  let symmetries =
    ([ s_poly * ri],
     [ [(v,w); (w,v)]       (* swap V and W *)
     ; [(m,m -@ one)]       (* message transformation *)
     ; [(v,v -@ one)]       (* v transformation *)
     ; [(w,w -@ one)]       (* w transformation *)
     ; [(v,v -@ w); (w,w)]  (* linear combinations *)
     ; [(v,w -@ v); (w,v)]  (* linear combinations *)

     ; [(v,v); (w,w -@ v)]  (* linear combinations *)
     ; [(v,w); (w,v -@ w)]  (* linear combinations *)

     ; [(v,v +@ w); (w,w)]  (* linear combinations *)
     ; [(v,w +@ v); (w,v)]  (* linear combinations *)

     ; [(v,v); (w,w +@ v)]  (* linear combinations *)
     ; [(v,w); (w,v +@ w)]  (* linear combinations *)
     ])
  in
  { sps_t = sps_t;
    choices = [0;1];
    vars = !vars;
    symmetries = symmetries;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = []
  }

(*******************************************************************)
(* \hd{Spec for both keys V,W in G1 and random, T = R + W in G2, and
       verification equation (T - W)*S = g(M,R,V,W)} *)

let spec3 () =
  let cS_v   = gen () in
  let cS_w   = gen () in
  let cS_m   = gen () in
  let cS_vm  = gen () in
  let cS_wm  = gen () in
  let cS_wt  = gen () in
  let cS_vt  = gen () in
  let cS_t   = gen () in
  let cS_tt  = gen () in
  let cS_tm  = gen () in
  let cS_1   = gen () in

  let t = r + w in
  let s_poly =
                       (* e(-,H)        e(-,T)        e(-,M) *)
  (* e(V,-) *)        (cS_v  * v)   + (cS_vt * v*t) + (cS_vm * v*m)
  (* e(W,-) *)      + (cS_w  * w)   + (cS_wt * w*t) + (cS_wm * w*m)
  (* e(phi(T),-) *) + (cS_t  * t)   + (cS_tt * t*t) + (cS_tm * t*m)
  (* e(phi(M),-) *) + (cS_m * m)      (* dupl.   *)   (* nocomp  *) 
  (* e(G,-)      *) + (cS_1 * one)    (* dupl.   *)   (* dupl.   *)
  in
  let sps_t =
    { sps_def with
      key_left    = [v;w];
      msg_right_n = ["M"];
      sig_right   = [ t; s_poly * ri ];
      sig_right_n = ["T"; "S"];
      setting     = TY2;
      osample     = ["R"]
    }
  in
  let nonzero_constrs = [ cS_vm + cS_wm + cS_m + cS_tm ] in (* m used *)
  let zero_constrs = [] in (* [ cS_rr * cS_wr ] in (* R + W is known *) *)
  let symmetries =
    ([t; s_poly * ri],
     [ [(v,w); (w,v)]       (* swap V and W *)
     ; [(m,m -@ one)]       (* message transformation *)
     ; [(v,v -@ one)]       (* v transformation *)
     ; [(w,w -@ one)]       (* w transformation *)
     ; [(v,v -@ w); (w,w)]  (* linear combinations *)
     ; [(v,w -@ v); (w,v)]  (* linear combinations *)

     ; [(v,v); (w,w -@ v)]  (* linear combinations *)
     ; [(v,w); (w,v -@ w)]  (* linear combinations *)

     ; [(v,v +@ w); (w,w)]  (* linear combinations *)
     ; [(v,w +@ v); (w,v)]  (* linear combinations *)

     ; [(v,v); (w,w +@ v)]  (* linear combinations *)
     ; [(v,w); (w,v +@ w)]  (* linear combinations *)
     ])
  in
  { sps_t = sps_t;
    choices = [0;1];
    vars = !vars;
    symmetries = symmetries;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = zero_constrs
  }

(* implement symmetry reduction:
   poly1 and poly2
   equivalent to poly1(V:=W, W:=V) and poly2...
   poly1(V:=V - W, W:=W) and poly2...
   poly1(V:=W - V, W:=W)
   poly1(V:=W - V, W:=V)
   and so on.

   Check for all these equivalent polynomials, if considered on is
   minimal (less or equal).
*)

(*******************************************************************)
(* \hd{Spec for both keys V,W in G1 and random, T = R + V + W in G2, and
       verification equation (T - W - V)*S = g(M,R,V,W)} *)

let spec4 () =
  let cS_v   = gen () in
  let cS_w   = gen () in
  let cS_m   = gen () in
  let cS_vm  = gen () in
  let cS_wm  = gen () in
  let cS_wr  = gen () in
  let cS_vr  = gen () in
  let cS_rr  = gen () in
  let cS_1   = gen () in

  let s_poly =
                       (* e(-,H)        e(-,R)        e(-,M) *)
  (* e(V,-) *)        (cS_v  * v)   + (cS_vr * v*r) + (cS_vm * v*m)
  (* e(W,-) *)      + (cS_w  * w)   + (cS_wr * w*r) + (cS_wm * w*m)
  (* e(phi(R),-) *)   (* 1 known *) + (cS_rr * r*r)   (* m known *)
  (* e(phi(M),-) *) + (cS_m * m)      (* m known *)   (* nocomp  *) 
  (* e(G,-)      *) + (cS_1 * one)    (* 1 known *)   (* dupl.   *)
  in
  let sps_t =
    { sps_def with
      key_left    = [v; w];
      msg_right_n = ["M"];
      sig_right   = [ r + w + v; s_poly * ri ];
      sig_right_n = ["T"; "S"];
      setting     = TY2;
      osample     = ["R"]
    }
  in
  let nonzero_constrs = [ cS_vm + cS_wm + cS_m ] in (* m used *)
  let zero_constrs = [ cS_rr * cS_wr * cS_vr ] in (* R + V + W is known *)
  let symmetries =
    ([r + w + v; s_poly * ri ],
     [ [(v,w); (w,v)]       (* swap V and W *)
     ; [(m,m -@ one)]       (* message transformation *)
     ; [(v,v -@ one)]       (* v transformation *)
     ; [(w,w -@ one)]       (* w transformation *)
     ; [(v,v -@ w); (w,w)]  (* linear combinations *)
     ; [(v,w -@ v); (w,v)]  (* linear combinations *)

     ; [(v,v); (w,w -@ v)]  (* linear combinations *)
     ; [(v,w); (w,v -@ w)]  (* linear combinations *)

     ; [(v,v +@ w); (w,w)]  (* linear combinations *)
     ; [(v,w +@ v); (w,v)]  (* linear combinations *)

     ; [(v,v); (w,w +@ v)]  (* linear combinations *)
     ; [(v,w); (w,v +@ w)]  (* linear combinations *)
     ])
  in
  { sps_t = sps_t;
    choices = [0;1];
    vars = !vars;
    symmetries = symmetries;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = zero_constrs
  }

(*******************************************************************)
(* \hd{Spec for both keys V,W in G1 and random, T = R + V + W in G2, and
       verification equation W*S = g(M,R,V,W)} *)

let spec5 () =
  let cS_v   = gen () in
  let cS_m   = gen () in
  let cS_vm  = gen () in
  let cS_vr  = gen () in
  let cS_r   = gen () in
  let cS_rr  = gen () in
  let cS_rm  = gen () in
  let cS_1   = gen () in

  let s_poly =
                       (* e(-,H)        e(-,R)          e(-,M) *)
  (* e(V,-) *)        (cS_v  * v)   + (cS_vr * v*r) + (cS_vm * v*m)
  (* e(W,-) *)        (* 1 known *)   (* R known *)   (* M known *)
  (* e(phi(R),-) *) + (cS_r * r)    + (cS_rr * r*r) + (cS_rm * r*m)
  (* e(phi(M),-) *) + (cS_m * m)      (* dupl.   *)   (* nocomp  *) 
  (* e(G,-)      *) + (cS_1 * one)    (* dupl.   *)   (* dupl.   *)
  in
  let sps_t =
    { sps_def with
      key_left    = [v; w];
      msg_right_n = ["M"];
      sig_right   = [ r; s_poly *@ wi ];
      sig_right_n = ["R"; "S"];
      setting     = TY2;
      osample     = ["R"]
    }
  in
  let nonzero_constrs = [ cS_vm + cS_rm + cS_m ] in (* m used *)
  let symmetries =
    ([ s_poly * wi],
     [ [(v,w); (w,v)]       (* swap V and W *)
     ; [(m,m -@ one)]       (* message transformation *)
     ; [(v,v -@ one)]       (* v transformation *)
     ; [(v,v -@ w); (w,w)]  (* linear combinations *)
     ; [(v,w -@ v); (w,v)]  (* linear combinations *)

     ; [(v,v +@ w); (w,w)]  (* linear combinations *)
     ; [(v,w +@ v); (w,v)]  (* linear combinations *)
     ])
  in
  { sps_t = sps_t;
    choices = [0;1];
    vars = !vars;
    symmetries = symmetries;
    nonzero_constrs = nonzero_constrs;
    zero_constrs = []
  }
