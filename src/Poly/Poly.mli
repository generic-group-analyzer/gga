(*s Module types [Var] and [Ring], [IntRing] implementation of [Ring], and
    [MakePoly] functor. *)

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
  val ladd : t list -> t
end

module IntRing : (Ring with type t = int)

module MakePoly : functor (V : Var) -> functor (C : Ring) ->
sig
  type t
  type var = V.t
  type coeff = C.t
  type monom
  type term
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
  val vars : t -> var list
  val partition : ((V.t list * C.t) -> bool) -> t -> (t * t)
  val to_terms : t -> (V.t list * C.t) list
  val from_terms : (V.t list * C.t) list -> t
  val is_const : t -> bool
  val is_var : t -> bool

  val ( *@) : t -> t -> t
  val (+@)  : t -> t -> t
  val (-@)  : t -> t -> t
end
