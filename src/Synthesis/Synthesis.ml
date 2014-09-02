(*s Synthesize SPS. *)

(*i*)
open Util
open Nondet
open LPoly
open LStringPoly
open InteractiveAnalyze
open SP

module IR = IntRing
(*i*)

(* \hd{Generate monomials} *)

(* \ic{We generate all exponent vectors $v$ for a vector $w$ of degree bounds.
       The enumeration algorithm is based on a ranking function that considers
       the vector $v$ as a mixed radix representation of a natural number with
       respect to the radix $w$.} *)

(* \ic{[vec_to_int r v] for the radix $r$ and the vector $v$ returns
       $\Sigma_{i=1}^{|r|} v_i\,(\Pi_{j=1}^{i-1} r_i)$.} *)

(*

let vec_to_int radix v =
  let rec go bs rs i mult =
    match bs,rs with
    | [],[] ->
      i
    | b::bs, r::rs ->
      go bs rs (i + mult*b) (mult*r)
    | _ ->
      failwith "dimensions of given vector and radix vector incompatible"
  in
  go v radix 0 1

(* \ic{[int_to_vec r i] is the inverse of [vec_to_int].} *)
let int_to_vec radix i =
  let rec go i rs v =
    match rs with
    | [] ->
      if i = 0 then Some (L.rev v) else None
    | r::rs ->
      go (i / r) rs ((i mod r)::v)
  in
  go i radix []

(* \ic{Generate all $k$-dimensional vectors $w \in \mathbb{N}^k$ such
       that $k = dim(v)$ and $w_i < v_i$ for all $i$.} *)
let vecs_smaller bvec =
  let rec go i =
    match int_to_vec bvec i with
    | Some v -> mplus (ret v) (go (succ i))
    | None   -> mempty
  in
  go 0

(* \hd{Recipe polynomials} *)

(* \ic{We use the following variables for recipe polynomials.} *)
type recipvar = M | V | W | R | S | One

let string_of_recipvar v = match v with
  | M -> "wM" | V -> "V" | W -> "W" | R -> "wR" | S -> "wS" | One -> "1"

(*i*)
let pp_recipvar fmt v = pp_string fmt (string_of_recipvar v)
(*i*)

(* \ic{Recipe polynomials.} *)
module RecipP = MakePoly(struct
  type t = recipvar
  let pp = pp_recipvar
  let equal = (=)
  let compare = compare
end) (IntRing)

(* \hd{Polynomials with random variables and messages} *)

type rmvar = V_M | V_V | V_W | V_R

(* \ic{We fix this order of random variables for our vector representation.} *)
let varorder = [V_V; V_W; V_R]

let string_of_rmvar v = match v with
  | V_M -> "M" | V_V -> "V" | V_W -> "W" | V_R -> "R"

(*i*)
let pp_rmvar fmt v = pp_string fmt (string_of_rmvar v)
(*i*)

(* \ic{Polynomials with random variables and messages.} *)
module RMP = MakePoly(struct
  type t = rmvar
  let pp = pp_rmvar
  let equal = (=)
  let compare = compare
end) (IntRing)

type rmpoly = RMP.t

(* \hd{Compute verification equation} *)

(* \ic{Simplify [inp] such that non-trivial linear relations are preserved:
       \begin{itemize}
       \item Remove duplicates
       \item Remove polynomials $f$ containing a monomial $m$ such that
         $m$ does not occur in any other polynomial. We know that they cannot
         be included in any non-trivial linear relation.
       \end{itemize}} *)
let simp_inp inp =
  let rec remove_dups left right =
    match right with
    | []                -> L.rev left
    | ((_,r1) as x)::xs ->
      if L.exists (fun (_,r2) -> RecipP.equal r1 r2) left
      then remove_dups left xs
      else remove_dups (x::left) xs
  in
  let not_contains_monom m (p,_) =
    IR.equal (RMP.coeff p m) IR.zero
  in
  let monom_unique ps m =
    L.for_all (not_contains_monom m) ps
  in
  let rec remove_unique_monom left right =
    match right with
    | []                  -> L.rev left
    | ((p,_) as x)::right ->
      begin match RMP.mons p with
      | _::_ as ms when L.exists (monom_unique (left@right)) ms ->
        remove_unique_monom left right
      | _ ->
        remove_unique_monom (x::left) right
      end
  in
  let inp = remove_dups [] inp in
  remove_unique_monom [] inp

(* \ic{Convert list of exponent vectors to [rmpoly].} *)
let evecs_to_poly vs =
  let evec_to_poly v =
    L.combine v varorder
    |> L.map (fun (e,v) -> RMP.var_exp v ( e - 1 )) (* also generate negative exponents *)
    |> RMP.lmult
  in
  RMP.ladd (L.map evec_to_poly vs)

(* \ic{Compute verification equation.} *)
let verif_eq s =

  (* \ic{ input in $\group_1$: $[1,V,W,R,S,M]$ } *)
  let inp_g1 =
    [ (RMP.one,     RecipP.var One)
    ; (RMP.var V_V, RecipP.var V)
    ; (RMP.var V_W, RecipP.var W)
    ; (RMP.var V_R, RecipP.var R)
    ; (s,           RecipP.var S)
    ; (RMP.var V_M, RecipP.var M)
    ]
  in

  (* \ic{ input in $\group_2$: $[1,R,S,M]$ } *)
  let inp_g2 =
    [ (RMP.one,     RecipP.var One)
    ; (RMP.var V_R, RecipP.var R)
    ; (s,           RecipP.var S)
    ; (RMP.var V_M, RecipP.var M)
    ]
  in

  (* \ic{ input in $\group_T$: [inp_g1 * inp_g2] minus redundancies } *)
  let inp_gt =
    inp_g1 @
    conc_map
      (fun (f2,r2) -> L.map (fun (f1,r1) -> (RMP.mult f1 f2, RecipP.mult r1 r2)) (L.tl inp_g1))
      (L.tl inp_g2)
  in
  let inp_gt = simp_inp inp_gt in

  (*i F.printf "GT: %a\n" (pp_list ", " (pp_pair RMP.pp RecipP.pp)) inp_gt; i*)
  
  let basis =
    conc_map (fun (p,_) -> RMP.mons p) inp_gt
    |> sorted_nub compare 
  in
  let coeff_vecs = L.map (fun (p,_) -> L.map (RMP.coeff p) basis) inp_gt in
  (*i F.printf "M:=\n";
      F.printf "%a\n" (pp_list "\n" (pp_list " " RMP.pp_coeff)) coeff_vecs; i*)
  let left_kernel = Pari_Ker.kernel coeff_vecs in
  (*
  let left_kernel = Sage_Solver.compute_kernel ?sts coeff_vecs in
  if left_kernel <> left_kernel' && L.map (L.map (fun x -> x * -1)) left_kernel <> left_kernel' then (
    F.printf "ker:\n%a\n" (pp_list ";\n " (pp_list ", " pp_int)) left_kernel;
    F.printf "ker':\n%a\n" (pp_list ";\n " (pp_list ", " pp_int)) left_kernel'
  );*)

  let recip_of_kernel vker =
    L.combine inp_gt vker
    |> L.map (fun ((_,r),c) -> RecipP.(from_int c *@ r))
    |> RecipP.ladd
  in
  L.map recip_of_kernel left_kernel

(* \hd{Analyze Scheme} *)

let to_gdef s veqs =
  fsprintf
    ("map G1 * G2 -> GT.\n"^^
     "iso G2 -> G1.\n"^^
     "input [V,W] in G1.\n"^^
     "oracle o1(M:G2) =\n"^^
     "  sample R;\n"^^
     "  return [ R, %a ] in G2.\n"^^
     "\n"^^
     "win (wM:G2, wR:G2, wS:G2) = (wM <> M /\\ 0 = %a).\n")
    RMP.pp s
    (pp_list " /\\ 0 = " RecipP.pp) veqs

let to_gdef_sigrand s veqs =
  let rename v = match v with
    | V_M -> SP.var "sM"
    | V_R -> SP.var "sR"
    | _   -> SP.var (string_of_rmvar v)
  in
  fsprintf
    ("map G1 * G2 -> GT.\n"^^
     "iso G2 -> G1.\n"^^
     "input [V,W] in G1.\n"^^
     "input [ sR, sM, %a ] in G2.\n"^^
     "oracle o1(M:G2) =\n"^^
     "  sample R;\n"^^
     "  return [ R, %a ] in G2.\n"^^
     "\n"^^
     "win (wM:G2, wR:G2, wS:G2) = (wM <> M /\\ wM <> sM /\\ 0 = %a).\n")
    SP.pp (RMP.to_terms s |> SP.eval_generic SP.const rename)
    RMP.pp s
    (pp_list " /\\ 0 = " RecipP.pp) veqs

    
let synth mt_f mt_g =
  let bounds = [3; 3; 4] in

  let i_verif   = ref 0 in
  let i_total   = ref 0 in
  let i_secure  = ref 0 in
  let i_unknown = ref 0 in
  let i_attack  = ref 0 in

  let offset v = List.map (fun x -> x - 1) v in
  (* let deg_vec_vw v = L.nth v 0 + L.nth v 1 in *)
  let deg_vec_v  v = L.nth v 0 in
  let deg_vec_w  v = L.nth v 1 in
  let deg_vec_r  v = L.nth v 2 in
  let sum_pos xs = L.fold_left (+) 0 (L.filter (fun i -> i > 0) xs) in

  (* \ic{Filters for search.} *)
  let sig_uses_sk f g =
       L.exists (fun v -> let v = offset v in deg_vec_v v <> 0) (f@g)
    && L.exists (fun v -> let v = offset v in deg_vec_w v <> 0) (f@g)
  in
  let sym_minimal f g =
    let swap_v_w m = match m with
      | [ x; y; z ] -> [ y; x; z]
      | _ -> failwith "impossible"
    in
    compare (L.map swap_v_w f,L.map swap_v_w g) (f,g) >= 0
  in
  let vecs =
    vecs_smaller bounds >>= fun vo ->
    let v = offset vo in
    guard (   (*i the monomial cannot be v^(0,0,0) = 1, for
                  f this would correspond to the monomial M and for g to the monomial 1 *)
              v <> [ 0; 0; 0 ]
              (*i Since V and W are in G1, V*W cannot be computed in GT i*)
           && not (L.nth v 0 = 1 && L.nth v 1 = 1)
              (* at most one value with negative exponent *)
           && L.length (L.filter (fun i -> i < 0) v) < 2
          ) >>
    ret vo
  in
  let vecs_f =
    vecs >>= fun v ->
    guard (   (* We cannot check a signature with terms where the sum of positive
                 degrees is > 1 for the variables since M consumes already one degree
                 in the verification equation *)
           let v = offset v in
           sum_pos v < 2
          ) >>
    ret v
  in
  let vecs_g =
    vecs >>= fun v ->
    guard (  let v = offset v in 
             (* g cannot be of the form h + r since the smaller signature h
                is equivalent wrt. to security (adversary can add/remove R to S) *)
              (v <> [ 0; 0; 1])
              (* not completely clear: at most one one multiplication *)
           && (sum_pos v <= 2)
          ) >>
    ret v
  in
  let sigs =
    cart (pick_set_exact mt_g vecs_f) (pick_set_exact mt_f vecs_g) >>= fun (f,g) ->
    guard (   (* this is 0, does not use M then *)
              f <> []
              (* if g is 0, then signature on M=0 is 0 *)
           && g <> []

           (* at most one negative exponent and not positive and negative occurence ( > 1 occurence for r) *)
           && not (L.exists (fun v -> let v = offset v in
                              (deg_vec_v v < 0) && (deg_vec_w v < 0 || deg_vec_r v < 0 || deg_vec_v v > 0)) (f@g))

            && not (L.exists (fun v -> let v = offset v in
                              (deg_vec_w v < 0) && (deg_vec_v v < 0 || deg_vec_r v < 0 || deg_vec_w v > 0)) (f@g))

            && not (L.exists (fun v -> let v = offset v in
                              (deg_vec_r v < 0) && (deg_vec_v v < 0 || deg_vec_w v < 0 || deg_vec_r v > 1)) (f@g))
            
              (* the signature must use either V or W *)
           && sig_uses_sk f g
              (* symmetry reduction, we choose (the smaller signature) in the
                 equivalence class obtained by renaming V to W *)
           && sym_minimal f g) >>
    ret (f,g)
  in

  (* \ic{Analyze a signature.} *)
  let analyze_sig (f,g) =
    incr i_total;
    let f = evecs_to_poly f in
    let g = evecs_to_poly g in
    let s = RMP.(f *@ (var V_M) +@ g) in
    let veqs = verif_eq s in
    if veqs = [] then (
      if !i_total mod 10 = 0 then F.printf "%i %!" !i_total
    ) else (
      incr i_verif;
      let sgdef = to_gdef s veqs in
      let res = analyze_bounded_from_string ~counter:true ~fmt:null_formatter sgdef 1 in
      match res with
      | Z3_Solver.Valid ->
        incr i_secure;
        F.printf "\n%i. S = %a, verif: %a\n%!" !i_secure RMP.pp s
          (pp_list " /\\ " (fun fmt p -> F.fprintf fmt "%a = 0" RecipP.pp p)) veqs;
        output_file (F.sprintf "./gen/%02i_%02i_%02i.ec" mt_f mt_g !i_secure) sgdef;
        output_file (F.sprintf "./gen/%02i_%02i_%02i_sigrand.ec" mt_f mt_g !i_secure) (to_gdef_sigrand s veqs)
      | Z3_Solver.Unknown ->
        if !i_total mod 10 = 0 then F.printf "\n%i? %!\n" !i_total;
        incr i_unknown
      | Z3_Solver.Attack _ ->
        output_file (F.sprintf "./gen/attack/%02i_%02i_%02i_attack.ec" mt_f mt_g !i_attack) sgdef;
        F.printf "\n%i! %!\n" !i_total;
        incr i_attack;
      | Z3_Solver.Error e ->
        F.printf "Error: %s\n" e;
        incr i_unknown
    )
  in

  (* \ic{Search process.} *)
  Pari_Ker.pari_init ();
  F.printf "Polynomials for variables %a and bounds %a <= v < %a:\n"
    (pp_list ", " pp_rmvar) varorder
    (pp_list ", " pp_int) (offset [ 0; 0; 0 ])
     (pp_list ", " pp_int) bounds;
  iter (-1) sigs analyze_sig;
  F.printf
    "\n%i Checked: %i no verification equation / %i secure / %i attack / %i unknown\n"
    !i_total (!i_total - !i_verif) !i_secure !i_attack  !i_unknown;
  output_file (F.sprintf "./gen/%02i_%02i_results" mt_f mt_g)
    (fsprintf
       "\n%10i;%04i;%04i;%04i;%04i\n"
       !i_total !i_verif !i_secure !i_attack  !i_unknown)
*)

module SPSPoly = SP

type setting = TY1 | TY2 | TY3

type sps_scheme = {
  key_left    : SPSPoly.t list;
  key_right   : SPSPoly.t list;
  msg_left    : SPSPoly.t list;
  msg_right   : SPSPoly.t list;
  sig_left    : SPSPoly.t list;
  sig_left_t  : SPSPoly.t list;
  sig_right   : SPSPoly.t list;
  sig_right_t : SPSPoly.t list;
  setting     : setting;
  oleft       : string list;
  oright      : string list;
  osample     : string list
}

let completion sps =
  let left = match sps.setting with
    | TY1 | TY2 -> sorted_nub compare (sps.key_left   @ sps.key_right @
                                       sps.msg_left   @ sps.msg_right @
                                       sps.sig_left_t @ sps.sig_right_t)
    | TY3 -> sorted_nub compare (sps.key_left @ sps.msg_left @ sps.sig_left_t)
  in
  let right = match sps.setting with
    | TY1 -> sorted_nub compare (sps.key_left   @ sps.key_right @
                                 sps.msg_left   @ sps.msg_right @
                                 sps.sig_left_t @ sps.sig_right_t)
    | TY2 | TY3 -> sorted_nub compare (sps.key_right @ sps.msg_right @ sps.sig_right_t)
  in
  let total_left  = SPSPoly.one :: left in
  let total_right = SPSPoly.one :: right in
  
  conc_map (fun l -> L.map (fun r -> l *@ r) total_right) total_left
  |> sorted_nub compare

let basis c =
  conc_map SPSPoly.mons c
  |> sorted_nub (fun x y -> compare (SPSPoly.from_mon x) (SPSPoly.from_mon y))

let poly_to_vector = SPSPoly.to_vector

let vector_to_poly v b =
  let rec loop acc v b =
    match (v,b) with
    | (x :: vs, y :: bs) -> loop (acc +@ ((SPSPoly.const x) *@ (SPSPoly.from_mon y)))
                                 vs bs
    | ([], []) -> acc
    | _ -> failwith "Vector and basis do not match."
  in
  loop SPSPoly.zero v b

let poly_list_to_matrix ps b =
  L.map (fun p -> poly_to_vector p b) ps

let pp_matrix m =
  L.map (fun l -> F.printf "| %a | \n" (pp_list ", " SPSPoly.pp_coeff) l) m

let kernel_to_eqns vs c =
  let vec_to_eqn v =
    let rec loop acc i w =
      match w with
      | [] -> acc
      | x :: ws -> loop (acc +@ ((SPSPoly.const x) *@ (L.nth c i))) (i+1) ws
    in
    loop SPSPoly.zero 0 v
  in
  L.map vec_to_eqn vs

let make_eval_map sps =
  let make_map vars vals =
    let z = L.combine vars vals in
    (fun x -> try L.assoc x z with _ -> SPSPoly.var x)
  in
  let vars : SPSPoly.var list = L.map (fun f -> L.hd (SPSPoly.vars f)) (sps.sig_left_t @ sps.sig_right_t) in
  make_map vars (sps.sig_left @ sps.sig_right)

let make_game sps vereqs : string =
  let gen_wc1 vs =
    let rec loop acc l = match l with
      | x :: xs -> let s = fsprintf "%a" SPSPoly.pp x in
                   let acc = if acc = "" then acc ^ "w" else acc ^ " /\\ w" in
                   loop (acc ^ s ^ " <> " ^ s) xs
      | [] -> acc
    in
    loop "" vs
  in
  (* Function for adding "w" in front of variables *)
  let rename =
    let l = sps.oleft @ sps.oright @ sps.osample in
    let ll = L.combine l (L.map (fun s -> SPSPoly.var ("w" ^ s)) l)
    in
    (fun x -> try L.assoc x ll with _ -> SPSPoly.var x)
  in 

  let preamble = match sps.setting with
    | TY1 -> "map G1 * G2 -> GT.\niso G1 -> G2.\niso G2 -> G1."
    | TY2 -> "map G1 * G2 -> GT.\niso G2 -> G1."
    | TY3 -> "map G1 * G1 -> GT."
  in
  let left = fsprintf "input [ %a ] in G1." (pp_list ", " SPSPoly.pp) sps.key_left in
  let right = fsprintf "input [ %a ] in G2." (pp_list ", " SPSPoly.pp) sps.key_right in
  let input = if sps.key_left = [] then
               (if sps.key_right = [] then ""
                else right)
             else (if sps.key_right = [] then left
                   else left ^ "\n" ^ right)
  in
  let opleft  = if sps.oleft = [] then ""
                else fsprintf "%a" (pp_list ":G1, " pp_string) sps.oleft ^ ":G1" in
  let opright = if sps.oright = [] then ""
                else fsprintf "%a" (pp_list ":G2, " pp_string) sps.oright ^ ":G2" in

  let oparam = if sps.oleft = [] then opright
               else opleft ^ ", " ^ opright in
  let osample = if sps.osample = [] then ""
                else fsprintf "  sample %a" (pp_list ";\n  sample " pp_string) sps.osample ^ ";" in
  let left = fsprintf "  return [ %a ] in G1." (pp_list ", " SPSPoly.pp) sps.sig_left in
  let right = fsprintf "  return [ %a ] in G2." (pp_list ", " SPSPoly.pp) sps.sig_right in
  let osig = if sps.sig_left = [] then
              (if sps.sig_right = [] then ""
               else right)
            else (if sps.sig_right = [] then left
                  else left ^ "\n" ^ right)
  in
  (* wM:G1 for each M in G1 and same for G2 *)
  let wpleft = if sps.msg_left = [] then ""
               else fsprintf "w%a" (pp_list ":G1, w" SPSPoly.pp) sps.msg_left ^ ":G1" in
  let wpright = if sps.msg_right = [] then ""
               else fsprintf "w%a" (pp_list ":G2, w" SPSPoly.pp) sps.msg_right ^ ":G2" in
  let wp_msg = if sps.msg_left = [] then wpright
           else wpleft ^ ", " ^ wpright in
  let wpleft = if sps.sig_left_t = [] then ""
               else fsprintf "w%a" (pp_list ":G1, w" SPSPoly.pp) sps.sig_left_t ^ ":G1" in
  let wpright = if sps.sig_right_t = [] then ""
               else fsprintf "w%a" (pp_list ":G2, w" SPSPoly.pp) sps.sig_right_t ^ ":G2" in
  let wp_sig = if sps.sig_left_t = [] then wpright
           else wpleft ^ ", " ^ wpright in
  let wp = if wp_msg = "" then wp_sig
           else wp_msg ^ ", " ^ wp_sig in
  
  let wc1 = gen_wc1 (sps.msg_left @ sps.msg_right) in
  let neqs = L.map (fun f -> SPSPoly.eval rename f) vereqs in
  let wc2 = fsprintf "0 = %a" (pp_list " /\\ 0 = " SPSPoly.pp) neqs in
  preamble ^ "\n\n" ^
  input ^
  "\n\noracle o1(" ^ oparam ^ ") =\n" ^ osample ^ "\n" ^ osig ^
  "\n\nwin(" ^ wp ^ ") =\n  (" ^ wc1 ^ " /\\ " ^ wc2 ^ ").\n"
 
let synth x y =
  let v = SPSPoly.var "V" in
  let w = SPSPoly.var "W" in
  let r = SPSPoly.var "R" in
  let m = SPSPoly.var "M" in
  let s = SPSPoly.var "S" in
  let vr = v *@ r in
  let wr = w *@ r in
  let rr = r *@ r in
  let mr = m *@ r in
  let vm = v *@ m in
  let wm = w *@ m in
  let mm = m *@ m in
  let vv = v *@ v in
  let wv = w *@ v in
  let ww = w *@ w in

  let sps = { 
              key_left    = [v; w];
              key_right   = [];
              msg_left    = [];
              msg_right   = [m];
              sig_left    = [];
              sig_left_t  = [];
              sig_right   = [r; v +@ rr +@ wm];
              sig_right_t = [r; s];
              setting     = TY2;
              oleft       = [];
              oright      = ["M"];
              osample     = ["R"; "T"];
            }
  in

  (* We follow our paper by computing a generic completion, then substitute for actual values *)
  let tmpl = completion sps in
  (* Substitute for actual value of s into the computed completion *)
  let c = L.map (SPSPoly.eval (make_eval_map sps)) tmpl in
  F.printf "%a\n" (pp_list ", " SPSPoly.pp) c;
  F.printf "%a\n" (pp_list ", " SPSPoly.pp) tmpl;
  let b = basis c in
  F.printf "%a\n" (pp_list ", " SPSPoly.pp) (L.map SPSPoly.from_mon b);
  let m = poly_list_to_matrix c b in
  pp_matrix m;
  Pari_Ker.pari_init ();
  let left_kernel = L.map (fun x -> L.map Big_int.big_int_of_int x) (Pari_Ker.kernel m) in
  F.printf "\n\n";
  pp_matrix left_kernel;
  let s : string = make_game sps (kernel_to_eqns left_kernel tmpl) in
  F.printf "%s" s;
  F.printf "\n%a" (pp_list "\n" SPSPoly.pp) (kernel_to_eqns left_kernel tmpl);
  F.printf "\n";
