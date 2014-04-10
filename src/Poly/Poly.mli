
module type Var = sig
  type t val pp : Format.formatter -> t -> unit
end

module type Ring = sig
  type t
  val pp : Format.formatter -> t -> unit
  val add : t -> t -> t
  val opp : t -> t
  val mult : t -> t -> t
  val one : t
  val zero : t
end

module MakePoly : functor (V : Var) -> functor (C : Ring) ->
sig
  type var = V.t
  type coeff = C.t
  type monom
  type term
  type t
  val pp_monom : Format.formatter -> monom -> unit
  val pp_term : Format.formatter -> term -> unit
  val pp : Format.formatter -> t -> unit
  val add : t -> t -> t
  val opp : t -> t
  val minus : t -> t -> t
  val mult : t -> t -> t
  val one : t
  val zero : 'a list
  val lmult : t list -> t
  val ladd : t list -> t
  val var : var -> t
  val const : coeff -> t
  val eval : (var -> t) -> t -> t
end

module IntRing : (Ring with type t = int)