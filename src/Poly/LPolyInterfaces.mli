(*s Module types for variables, ring, and polynomials
    shared between [LPoly.ml] and [LPoly.mli]. *)

module type Var = sig
  type t
  val pp : Format.formatter -> t -> unit
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module type Ring = sig
  type t
  val pp : Format.formatter -> t -> unit
  val add : t -> t -> t
  val opp : t -> t
  val mult : t -> t -> t
  val ring_exp : t -> int -> t
  val one : t
  val zero : t
  val ladd : t list -> t
  val from_int : int -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val use_parens : bool
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
  val pp_break : Format.formatter -> t -> unit
  val pp_coeff : Format.formatter -> coeff -> unit
  val add : t -> t -> t
  val opp : t -> t
  val minus : t -> t -> t
  val mult : t -> t -> t
  val ring_exp : t -> int -> t
  val var_exp : var -> int -> t
  val one : t
  val zero : t
  val lmult : t list -> t
  val ladd : t list -> t
  val var : var -> t
  val const : coeff -> t
  val from_int : int -> t

  (* \ic{[eval env f] returns the polynomial [f] evaluated at
         the points [x := env x].} *)
  val eval : (var -> t) -> t -> t
  val eval_generic : ('c -> t) -> ('v -> t) -> (('v * int) list * 'c) list -> t
  val vars : t -> var list

  (* \ic{[partition p f] returns a tuple [(t1s,t2s)]
         where [t1s] consists of the terms of [f] satisfying [p]
         and [t1s] consists of the terms of [f] not satisfying [p].} *)
  val partition : (((var * int) list * coeff) -> bool) -> t -> (t * t)
  val to_terms : t -> ((var * int) list * coeff) list
  val from_terms : ((var * int) list * coeff) list -> t
  val from_mon : monom -> t
  val is_const : t -> bool
  val is_var : t -> bool

  val mons : t -> monom list
  val coeff : t -> monom -> coeff

  (* In the tool we want to express a polynomial in terms of a monomial basis *)
  val to_vector : t -> monom list -> coeff list

  val div_mon : t -> monom -> t
  val ggt_mon : monom -> monom -> monom

  val ( *@) : t -> t -> t
  val (+@)  : t -> t -> t
  val (-@)  : t -> t -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
end
