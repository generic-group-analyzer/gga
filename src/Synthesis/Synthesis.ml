(*s Synthesize SPS. *)

(*i*)
open Util
(*i*)

(* \hd{Generate polynomials} *)

(* \ic{Generate all $k$-dimensional vectors $w \in \mathbb{N}^k$ such
       that $k = dim(v)$ and $w_i < v_i$ for all $i$.
       We use consider the vector $v$ as a mixed radix representation
       with respect to the radix $w$.} *)


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

let int_to_vec radix i0 =
  let rec go i rs v =
    match rs with
    | [] ->
      if i = 0 then Some (List.rev v) else None
    | r::rs ->
      go (i / r) rs ((i mod r)::v)
  in
  go i0 radix []

let vecs_smaller bvec =
  let ub = vec_to_int bvec bvec in
  let rec go i =
    match int_to_vec bvec i with
    | Some v -> Nondet.mplus (Nondet.ret v) (go (succ i))
    | None   -> Nondet.mempty
  in go 0

(* \hd{Compute verification equation} *)

(* \hd{Analyze Scheme} *)

let synth () =
  F.printf "Exponent vectors for v,w,r:\n";
  Nondet.iter (-1) (vecs_smaller [2;2;3])
    (fun v -> F.printf "[%a]\n" (pp_list "," pp_int) v)

let test () =
  let radix = [ 2; 2; 3 ] in
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