(*s Input for non-parametric problems.\\ *)

(*i*)
open Util
open Poly
(*i*)

(*******************************************************************)
(* \hd{Group settings, group elements, and assumptions} *)

(* \ic{Each group has an identifier.} *)
type group_id = string

(* \ic{An isomorphism has a domain and a codomain.} *)
type iso = {
  iso_dom   : group_id;
  iso_codom : group_id
}

(* \ic{A multi-linear map has a domain and a codomain.} *)
type emap = {
  em_dom   : group_id list;
  em_codom : group_id
}

(* \ic{%
   A group setting consists of group identifiers,
   isomorphisms, and multilinear maps.} *)
type group_setting = {
  gs_group_ids : group_id list;
  gs_isoms     : iso list;
  gs_emaps     : emap list
}

(* \ic{We use strings for random variables such as $X$. } *)
type rvar = string

(* \ic{Random polyomials such as $X*X + Y$.} *)
module RP = MakePoly(struct
  type t = rvar
  let pp = pp_string
  let equal = (=)
  let compare = compare
end) (IntRing)

type rpoly = RP.t

(* \ic{We model a group element as a random polynomial and a group identifier.} *)
type group_elem = {
  ge_rpoly : rpoly;
  ge_group : group_id;
}

(* \ic{%
   A non-parametric \emph{computational assumption} consists of the group setting,
   the list of adversary inputs, and the challenge.
   A non-parametric \emph{decisional assumption} consists of the group setting,
   the left adversary input, and the right adversary input.} *)
type assumption =
  | Computational of group_setting * rpoly list * rpoly
  | Decisional    of group_setting * rpoly list * rpoly list


(*******************************************************************)
(* \hd{Pretty printing} *)

let pp_isom fmt i =
  F.fprintf fmt "phi : %s -> %s" i.iso_dom i.iso_codom

let pp_emap fmt e =
  F.fprintf fmt "e : %a -> %s" (pp_list "x" pp_string) e.em_dom e.em_codom




let init () =
  F.printf "NonParamInput initialized\n%!"
