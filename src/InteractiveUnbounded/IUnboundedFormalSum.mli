open Poly

type db_idx = int

type input_idx = int

type oreturn_idx = int

type orvar_id = IUnboundedInput.orvar_id * IUnboundedInput.oname

type oparam_id = IUnboundedInput.oparam_id * IUnboundedInput.oname

type var = SRVar of IUnboundedInput.rvar_id | ORVar of orvar_id * db_idx

type param =
  | OParam of oparam_id * db_idx
  | FieldChoice of IUnboundedInput.fchoice_id
  | ICoeff of IUnboundedInput.gchoice_id * input_idx
  | OCoeff of IUnboundedInput.gchoice_id * IUnboundedInput.oname * oreturn_idx * db_idx

type t

val plus : t -> t -> t

val opp : t -> t

val mult : t -> t -> t

val const : IntRing.t -> t

val zero : t

val param : param -> t

val var : var -> t

val one : t

val ( *& ) : t -> t -> t

val ( +& ) : t -> t -> t

val of_terms : (IntRing.t *  param list * var list) list -> t

val of_coeff : IntRing.t -> t

val of_var : var -> t

val of_param : param -> t

type fs_param = (IntRing.t * param list) list

type fs_rvars = (fs_param * var list) list

val fs_to_fs_rvars : t -> fs_rvars

type param_constr = (db_idx * IUnboundedInput.oname) list * fs_param

val fs_to_constr : t -> ((db_idx * IUnboundedInput.oname) list * fs_param) list

val fs_to_bounded_constr : 'a -> 'b -> 'c list

val compare_fsp : fs_param -> fs_param -> int

val equal_fsp : fs_param -> fs_param -> bool

val compare_constr : param_constr -> param_constr -> int

val equal_constr : param_constr -> param_constr -> bool

(**********************************************************************)
(* Pretty printing *)

val pp_var : Util.F.formatter -> var -> unit

val pp_param : Util.F.formatter -> param -> unit

val pp_monom : Util.F.formatter -> var list -> unit

val pp_params : Util.F.formatter -> param list -> unit

val pp_term : Util.F.formatter -> IntRing.t * param list * var list -> unit

val pp_fsum : Util.F.formatter -> t -> unit

val pp_param_constr :
  string -> Util.F.formatter -> (int * string) list * fs_param -> unit

val pp_param_constr_ineq :
  Util.F.formatter -> (int * string) list * fs_param -> unit

val pp_fs_rvars :
  Util.F.formatter -> fs_rvars -> unit

(* type term = IntRing.t * param list * var list *)

(* val term_compare : IntRing.t * 'a * 'b -> IntRing.t * 'a * 'b -> int *)

(* val db_idx_of_var : var -> (int * IUnboundedInput.oname) option *)

val db_idx_of_param : param -> (int * IUnboundedInput.oname) option

(* val db_idx_of_term : param list -> var list -> (int * IUnboundedInput.oname) list *)

(* val map_idx_var : (int -> int) -> var -> var *)

(* val map_idx_param : (int -> int) -> param -> param *)

(* val shift_var : int -> var -> var *)

(* val shift_param : int -> param -> param *)

(* val implicit_ineqs : var list -> int list list *)

(* val canonical_renaming : var list -> param list -> (int * int) list *)

(* val missing_ineq : int list list -> int list list -> Util.Sii.elt option *)

(* val db_idx_subst_var : (int * int) list -> var -> var *)

(* val db_idx_subst_param : (int * int) list -> param -> param *)

(* val db_idx_subst_ineqs : ('a * 'a) list -> 'a list list -> 'a list list *)

(* val simp_ineqs : 'a list list -> 'a list list *)

(*   type raw_term = term * db_idx list list

  val mult_raw_term :
      IntRing.t * param list * var list ->
      IntRing.t * param list * var list ->
      (IntRing.t * param list * var list) * int list list
  val terms_of_raw_term :
      ('a * param list * var list) * int list list ->
      ('a * param list * var list) list
  val mult_fs_term :
      (IntRing.t * param list * var list) list ->
      IntRing.t * param list * var list -> (IntRing.t * param list * var list) list
 *)

(* val monoms : ('a * 'b * 'c) list -> 'c list *)

(* val coeff : (IntRing.t * param list * 'a) list -> 'a -> fs_param *)

(* val fs_to_fs_rvars : (IntRing.t * param list * var list) list -> fs_rvars *)

