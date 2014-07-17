(*s Synthesize SPS. *)

(*i*)
open Util
(*i*)

(* \hd{Generate monomials} *)

(* \ic{We generate all exponent vectors $v$ for a degree bound vector $w$.
       The enumeration algorithm considers the vector $v$ as a mixed radix
       representation of a natural number with respect to the radix $w$.} *)

(* \ic{For radix $r$ and vector $v$, the result is
       $\Sigma_{i=1}^{|r|} v_i\,(\Pi_{j=1}^{i-1} r_i)$.} *)
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

(* \ic{The inverse of [vec_to_int].} *)
let int_to_vec radix i0 =
  let rec go i rs v =
    match rs with
    | [] ->
      if i = 0 then Some (List.rev v) else None
    | r::rs ->
      go (i / r) rs ((i mod r)::v)
  in
  go i0 radix []

(* \ic{Generate all $k$-dimensional vectors $w \in \mathbb{N}^k$ such
       that $k = dim(v)$ and $w_i < v_i$ for all $i$.} *)
let vecs_smaller bvec =
  let rec go i =
    match int_to_vec bvec i with
    | Some v -> Nondet.mplus (Nondet.ret v) (go (succ i))
    | None   -> Nondet.mempty
  in go 1

(* \hd{Combinators for generation} *)

(* \ic{Return all subsets $S$ of $m$ such that $|S| \leq k$.} *)
let pick_set k m =
  let rec go k acc =
    Nondet.(
      mplus
        (ret acc)
        (if k = 0 then mempty
         else m >>= fun x ->
              guard ((List.for_all (fun y -> y < x) acc)) >>
              go (k-1) (x::acc))
    )
  in
  go k []

(* \ic{Return the cartesian product of $m1$ and $m2$.} *)
let cart m1 m2 =
  Nondet.(
    m1 >>= fun x1 ->
    m2 >>= fun x2 ->
    ret (x1,x2)
  )

(* \ic{Return the cartesian product of $m$.} *)
let prod m = cart m m

(* \ic{Return the $n$-fold cartesian product of $ms$.} *)
let rec ncart ms =
  match ms with
  | []    -> Nondet.ret []
  | m::ms ->
    Nondet.(
      m >>= fun x ->
      ncart ms >>= fun xs ->
      ret (x::xs)
    )

(* \hd{Compute verification equation} *)

(* \hd{Analyze Scheme} *)

let pp_mon vars fmt v =
  let ev =
    L.filter (fun (e,_) -> e > 0) (List.combine v vars)
  in
  let pp_vp fmt (e,v) =
    if e = 1 then F.fprintf fmt "%s" v
    else F.fprintf fmt "%s^%i" v e
  in
  F.fprintf fmt "%a" (pp_list "*" pp_vp) ev

let pp_poly vars fmt f =
  F.fprintf fmt "%a" (pp_list " + " (pp_mon vars)) f

let synth () =
  let vars = ["v"; "w"; "r"] in
  let bounds = [3; 3; 3] in
  let i = ref 0 in
  F.printf "Polynomials for variables %a and bounds %a:\n"
    (pp_list ", " pp_string) vars
    (pp_list ", " pp_int) bounds;
  Nondet.iter (-1)
    (prod (pick_set 2 (vecs_smaller bounds)))
    (fun (f,g) ->
       incr i;
       F.printf "%i. f = %a, g = %a\n" !i (pp_poly vars) f (pp_poly vars) g)

let test () =
  let radix = [ 3; 3; 3 ] in
  let v2i = vec_to_int radix in
  let i2v = int_to_vec radix in
  let pr i =
    F.printf "%a\n" (pp_opt pp_int) (map_opt v2i (i2v i))
  in
  pr 5;
  pr 6;
  pr 7;
  pr 8;
  pr 9;
  pr 10;
  pr 11