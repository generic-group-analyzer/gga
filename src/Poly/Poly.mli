(*s [IntRing] implementation of [Ring] and [MakePoly] functor. *)

open PolyInterfaces

module IntRing : (Ring with type t = int)

module MakePoly (V : Var) (C : Ring) : Poly with type var = V.t and type coeff = C.t 
