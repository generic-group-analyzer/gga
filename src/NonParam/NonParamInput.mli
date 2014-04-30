(*s Input for non-parametric problems.\\ *)

(*i*)
open Util
(*i*)

(*******************************************************************)
(* \hd{Group settings, group elements, and assumptions} *)

(* \ic{Each group has an identifier.} *)
type group_id = string

(* \ic{An isomorphism has a domain and a codomain.} *)
type iso = { iso_dom : group_id; iso_codom : group_id; }

(* \ic{A multi-linear map has a domain and a codomain.} *)
type emap = { em_dom : group_id list; em_codom : group_id; }

(* \ic{A group setting consists of isomorphisms and multilinear maps.
       Group ids are implicit.\\
     {\bf COMPOSITE:} add [gs_prime_num : int] } *)
type group_setting = { gs_isos : iso list; gs_emaps : emap list; }

(* \ic{%
   A closed group setting consists of isomorphisms, multilinear maps,
   the target group, and the set of group ids. It has been validated. \\
   {\bf COMPOSITE}: add [cgs_prime_num : int]} *)
type closed_group_setting = private {
  cgs_isos : iso list;
  cgs_emaps : emap list;
  cgs_target : group_id;
  cgs_gids : Ss.t;
}

(* \ic{Random polyomials such as $X*X + Y$.} *)
type rvar = string

(* \ic{Random polyomials such as $X*X + Y$.} *)
module RP : PolyInterfaces.Poly with type var = rvar and type coeff = Big_int.big_int

type rpoly = RP.t

(* \ic{[rp_to_vector mon_basis f] converts [f] to a coefficient vector with respect to the
   monomial basis [mon_basis]. We do not check if [f] contains monomials not included in [mon_basis].} *)
val rp_to_vector : RP.monom list -> rpoly -> RP.coeff list

(* \ic{We model a group element as a random polynomial and a group identifier.\\
   {\bf COMPOSITE}: change [ge_rpolys : rpoly list]} *)
type group_elem = { ge_rpoly : rpoly; ge_group : group_id; }

val shape: group_elem list -> group_id list

(* \ic{%
   A non-parametric \emph{computational assumption} consists of the group setting,
   the list of adversary inputs, and the challenge.
   A non-parametric \emph{decisional assumption} consists of the group setting,
   the left adversary input, and the right adversary input.} *)
type assumption = private
  | Computational of closed_group_setting * group_elem list * group_elem
  | Decisional    of closed_group_setting * group_elem list * group_elem list

(*******************************************************************)
(* \hd{Smart constructors for group settings and assumptions} *)

(* \ic{The given assumption is invalid.} *)
exception InvalidAssumption of string

(* \ic{Fail because assumption is invalid.} *)
val fail_assm : string -> 'a

(* \ic{Validate grout setting and create closed group setting.} *)
val close_group_setting : group_setting -> closed_group_setting

(* \ic{Create group setting for generic group (no isomorphisms and no maps, single group).
   {\bf COMPOSITE}: add [int] for [prime_num]} *)
val closed_generic_group : group_id -> closed_group_setting

(* \ic{Create computational assumption.} *)
val mk_computational :
  closed_group_setting -> group_elem list -> group_elem -> assumption

(* \ic{Create decisional assumption.} *)
val mk_decisional :
  closed_group_setting -> group_elem list -> group_elem list -> assumption

(*******************************************************************)
(* \hd{Commands for building assumptions} *)

type cmd =
  | AddIsos of iso list
  | AddMaps of emap list
  | AddInputLeft of group_elem list
  | AddInputRight of group_elem list
  | AddInput of group_elem list
  | SetChallenge of group_elem

type incomp_assm = {
  ia_gs            : group_setting;
  ia_is_decisional : bool option;
  ia_input_left    : group_elem list;
  ia_input_right   : group_elem list;
  ia_input         : group_elem list;
  ia_challenge     : group_elem option;
}

val empty_ias : incomp_assm

val handle_cmd : cmd -> incomp_assm -> incomp_assm

val eval_cmds : cmd list -> assumption

(*i*)
val pp_iso        : F.formatter -> iso           -> unit
val pp_emap       : F.formatter -> emap          -> unit
val pp_iso_s      : F.formatter -> iso           -> unit
val pp_emap_s     : F.formatter -> emap          -> unit
val pp_group_id   : F.formatter -> group_id      -> unit
val pp_group_elem : F.formatter -> group_elem    -> unit
val pp_gs         : F.formatter -> group_setting -> unit
val pp_cmd        : F.formatter -> cmd           -> unit
(*i*)

(*i*)
(* Only for testing *)
module Internals : sig
  val gs_is_cyclic : group_setting -> bool
end
(*i*)
