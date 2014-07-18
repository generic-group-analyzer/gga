(*s Synthesize SPS. *)

(*i*)
open Util
open Nondet
(*i*)

(* \hd{Generate monomials} *)

(* \ic{We generate all exponent vectors $v$ for a degree bound vector $w$.
       The enumeration algorithm considers the vector $v$ as a mixed radix
       representation of a natural number with respect to the radix $w$.} *)

(* \ic{[vec_to_int r v] for the radix $r$ and the vector $v$ returns
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
  go 1

(* \hd{Compute verification equation} *)

(* \hd{Analyze Scheme} *)

let pp_mon vars fmt v =
  let ev =
    L.filter (fun (e,_) -> e > 0) (L.combine v vars)
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
  let max_terms = 2 in
  let i = ref 0 in
  F.printf "Polynomials for variables %a and bounds %a:\n"
    (pp_list ", " pp_string) vars
    (pp_list ", " pp_int) bounds;
  iter (-1)
    (prod (pick_set max_terms (vecs_smaller bounds)))
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