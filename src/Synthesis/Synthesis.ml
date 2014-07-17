(*s Synthesize SPS. *)

(*i*)
open Util
(*i*)

(* \hd{Generate polynomials} *)

(* \ic{Generate all $k$-dimensional vectors $w \in \mathbb{N}^k$ such
       that $k = dim(v)$ and $w_i \leq v_i$ for all $i$.
       We use consider the vector $v$ as a mixed radix representation
       with respect to the radix $w$.} *)


let vec_to_int radix0 v0 =
  let go v radix acc =
    match v,radix with
    | [],[] ->
      acc
    | b::bs, r::rs ->
      failwith "undefined"
    | _ ->
      failwith "dimensions of given vector and radix vector incompatible"
  in
  go v0 radix0 0

let int_to_vec radix0 i0 =
  let go i radix acc =
    match radix with
    | [] ->
      acc
    | r::rs ->
      failwith "undefined"
  in
  go i0 radix0 []


let vecs_smaller bvec =
  let ub = vec_to_int bvec bvec in
  let rec go i =
    Nondet.mplus
      (Nondet.ret (int_to_vec bvec i))
      (if i < ub then go (succ i) else Nondet.mempty)
  in go 1

(* \hd{Compute verification equation} *)

(* \hd{Analyze Scheme} *)

let synth () =
  F.printf "Exponent vector for v,w,r:\n";
  Nondet.iter (-1) (vecs_smaller [])
    (fun v -> F.printf "[%a]\n" (pp_list "," pp_int) v)
