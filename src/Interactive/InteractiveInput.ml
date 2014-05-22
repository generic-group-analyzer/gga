(*s Input for interactive assumptions. We assume that there is only one group for now, i.e., the setting
       is equivalent to the generic group setting.
%  
       Note that this is the case for most computational problems where
       a bilinear map that does not occur in the input, oracle, and
       winning definition is useless *)
(*i*)
open Util
open Poly
(*i*)

(*******************************************************************)
(* \hd{Adversary input} *)

(* \ic{For the adversary input, we use polynomials in $\mathcal{Z}[\vec{X}]$
       for random variables $\vec{X}$.} *)

type rvar_id = string

module RP = MakePoly(struct
  type t = rvar_id
  let pp = pp_string
  let equal = (=)
  let compare = compare
end) (IntRing)

(*******************************************************************)
(* \hd{Oracle definitions} *)

(* \ic{For the oracle return values, we use polynomials in
       $\mathcal{Z}[\vec{X},\vec{A},\vec{m}]$ where
       $\vec{X}$ are shared (initially sampled) random variables,
       $\vec{A}$ are random variables sampled in the oracle,
       $\vec{m}$ are oracle arguments in $\field$.
       The oracle is then implicitly defined given such a polynomial $f$:
       Take (named) parameters $\vec{m} = params(f)$,
       sample $\vec{A} = freshvars(f)$,
       return $f(\vec{X}, \vec{A}, \vec{m})$.} *)
type ovar_id = string

(* \ic{Variables in oracle polynomials.} *)
type ovar = 
  | Param of ovar_id
  | GRVar of ovar_id
  | FRVar of ovar_id

let string_of_ovar v = match v with
  | Param s | GRVar s | FRVar s -> s

let pp_ovar fmt v = pp_string fmt (string_of_ovar v)

(* \ic{Oracle polynomials.} *)
module OP = MakePoly(struct
  type t = ovar
  let pp = pp_ovar
  let equal = (=)
  let compare = compare
end) (IntRing)

type opoly = OP.t

(* \ic{An oracle definition is just a list of oracle polynomials
       using the interpretation given above.} *) 
type odef = opoly list

(*******************************************************************)
(* \hd{Winning condition definition} *)

(* \ic{A winning condition is given by two sets of polynomials,
   one set that is interpreted as the required equalities and one set
   interpreted as the required inequalities.
   These polynomials are in $\mathcal{Z}[\vec{X},\vec{U},\vec{w},\vec{m}]$
   where $\vec{X}$ denotes the random variables, $\vec{U}$ denotes the
   adversary choices in $\group$, $\vec{w}$ denotes the adversary choices
   in $\field$, and $\vec{m}$ denotes the oracle arguments.
   Every polynomial containing oracle argument variables $m$ is
   interpreted as $\forall i \in [q]. f(\ldots,m_i,\ldots) \neq 0$ (resp. $=$).} *)

type wvar_id = string

(* \ic{Variables in winning condition polynomials.} *)
type wvar = 
  | FieldChoice of wvar_id
  | GroupChoice of wvar_id
  | OArg        of wvar_id
  | RVar       of wvar_id

let string_of_wvar v = match v with
  | FieldChoice s | GroupChoice s | OArg s | RVar s -> s

let pp_wvar fmt v = pp_string fmt (string_of_wvar v)

(* \ic{Winning condition polynomials.} *)
module WP = MakePoly(struct
  type t = wvar
  let pp = pp_wvar
  let equal = (=)
  let compare = compare
end) (IntRing)

type wpoly = WP.t

(* \ic{A winning condition consists of a list of equalities and a list
       of inequalities.} *) 
type wcond = {
  wcond_eqs   : wpoly list;
  wcond_ineqs : wpoly list;
}


let f () =
  F.printf "Hello\n\n"