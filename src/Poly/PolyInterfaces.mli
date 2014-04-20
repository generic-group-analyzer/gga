(*s Module types for variables, ring, and polynomial
    shared between Poly.ml and Poly.mli *)

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

module type Poly = sig
  type t
  type var
  type coeff
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

  (* \ic{[eval env f] returns the polynomial [f] evaluated at
         the points [x := env x].} *)
  val eval : (var -> t) -> t -> t
  val vars : t -> var list

  (* \ic{[partition p f] returns a tuple [(t1s,t2s)]
         where [t1s] consists of the terms of [f] satisfying [p]
         and [t1s] consists of the terms of [f] not satisfying [p].} *)
  val partition : ((var list * coeff) -> bool) -> t -> (t * t)
  val to_terms : t -> (var list * coeff) list
  val from_terms : (var list * coeff) list -> t
  val is_const : t -> bool
  val is_var : t -> bool

  val ( *@) : t -> t -> t
  val (+@)  : t -> t -> t
  val (-@)  : t -> t -> t
end
