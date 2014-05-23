(* s Input for interactive assumptions. We assume that there is only one group for now, i.e., the setting
       is equivalent to the generic group setting.
%  
       Note that this is the case for most computational problems where
       a bilinear map that does not occur in the input, oracle, and
       winning definition is useless. *)
(*i*)
open Util
open Poly
(*i*)

(*******************************************************************)
(* \hd{Adversary input definition} *)

(* \ic{For the adversary input, we use polynomials in $\ZZ[\vec{X}]$
       for random variables $\vec{X}$.} *)

type rvar_id = string

module RP = MakePoly(struct
  type t = rvar_id
  let pp = pp_string
  let equal = (=)
  let compare = compare
end) (IntRing)

type rpoly = RP.t

(*******************************************************************)
(* \hd{Oracle definitions} *)

(* \ic{For the oracle return values, we use polynomials in
       $\ZZ[\vec{X},\vec{A},\vec{m}]$ where
       $\vec{X}$ are shared (initially sampled) random variables,
       $\vec{A}$ are random variables sampled in the oracle,
       $\vec{m}$ are oracle arguments in $\field$.
       The oracle is then implicitly defined as follows by such a vector of polynomials $\vec{f}$:\\
       Take (named) parameters $\vec{m} = params(\vec{f})$ as inputs,
       sample $\vec{A} = freshvars(\vec{f})$ in $\group$,
       return $(f_1(\vec{X}, \vec{A}, \vec{m}),\ldots,
                f_{|\vec{f}|}(\vec{X}, \vec{A}, \vec{m}))$.} *)
type ovar_id = string

(* \ic{Variables in oracle polynomials.} *)
type ovar = 
  | Param of ovar_id
  | SRVar of ovar_id
  | ORVar of ovar_id

let string_of_ovar v = match v with
  | Param s | SRVar s | ORVar s -> s

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

let pp_opoly fmt opolys =
  let get_param v = match v with Param s -> [s] | _ -> [] in
  let get_orvar v = match v with ORVar s -> [s] | _ -> [] in
  let params = conc_map (fun f -> conc_map get_param (OP.vars f)) opolys in
  let orvars = conc_map (fun f -> conc_map get_orvar (OP.vars f)) opolys in
  F.fprintf fmt "(%a) = %a; return (%a)"
    (pp_list ", " (fun fmt -> F.fprintf fmt "%s:Fq")) params
    (pp_list "; " (fun fmt -> F.fprintf fmt "%s <-$ G")) orvars
    (pp_list ", " OP.pp) opolys

(*******************************************************************)
(* \hd{Winning condition definition} *)

(* \ic{A winning condition is given by two sets of polynomials,
   one set that is interpreted as the required equalities and one set
   interpreted as the required inequalities.
   These polynomials are in $\ZZ[\vec{X},\vec{U},\vec{w},\vec{m}]$
   where $\vec{X}$ denotes the random variables, $\vec{U}$ denotes the
   adversary choices in $\group$, $\vec{w}$ denotes the adversary choices
   in $\field$, and $\vec{m}$ denotes the oracle arguments.
   Every inequality (resp. equality) polynomial containing oracle argument
   variables~$m$ is interpreted as
   $\forall i \in [q]: f(\ldots,m_i,\ldots) \neq 0$ (resp. $=$).} *)

type wvar_id = string

(* \ic{Variables in winning condition polynomials.} *)
type wvar = 
  | FieldChoice of wvar_id
  | GroupChoice of wvar_id
  | OArg        of wvar_id
  | RVar        of wvar_id

let string_of_wvar v = match v with
  | FieldChoice s | GroupChoice s | RVar s -> s
  | OArg s -> s^"_i"

let pp_wvar fmt v = pp_string fmt (string_of_wvar v)

(* \ic{Winning condition polynomials.} *)
module WP = MakePoly(struct
  type t = wvar
  let pp = pp_wvar
  let equal = (=)
  let compare = compare
end) (IntRing)

type wpoly = WP.t

let pp_wpoly fmt wp =
  if L.exists (function OArg _ -> true | _ -> false) (WP.vars wp) then
    F.fprintf fmt "forall i: %a" WP.pp wp
  else
    WP.pp fmt wp

(* \ic{A winning condition consists of a list of equalities and a list
       of inequalities.} *) 
type wcond = {
  wcond_eqs   : wpoly list;
  wcond_ineqs : wpoly list;
}

let pp_eq fmt = F.fprintf fmt "%a = 0" pp_wpoly

let pp_ineq fmt = F.fprintf fmt "%a <> 0" pp_wpoly

let pp_wcond_conds fmt wcond =
  let pp_eqs = pp_list " /\\ " pp_eq in
  let pp_ineqs = pp_list " /\\ " pp_ineq in
  match wcond.wcond_eqs, wcond.wcond_ineqs with
  | [], []     -> F.fprintf fmt "true"
  | eqs, []    -> F.fprintf fmt "%a" pp_eqs eqs
  | [], ineqs  -> F.fprintf fmt "%a" pp_ineqs ineqs
  | eqs, ineqs -> F.fprintf fmt "%a /\\ %a" pp_eqs eqs pp_ineqs ineqs

let pp_wcond fmt wcond =
  let fold_vars g =
    wcond.wcond_eqs @ wcond.wcond_ineqs
    |> conc_map (fun f -> conc_map g (WP.vars f))
    |> sorted_nub compare
  in
  let pp_ty_list ty fmt ns =
    pp_list ", " pp_string fmt (L.map (fun n -> n^":"^ty) ns)
  in
  let pp_args fmt (gchoices,fchoices) = match gchoices, fchoices with
    | [], [] -> F.fprintf fmt ""
    | [], _  -> pp_ty_list "G" fmt gchoices
    | _, []  -> pp_ty_list "G" fmt gchoices
    | _, _   -> F.fprintf fmt "%a, %a" (pp_ty_list "G")  gchoices (pp_ty_list "Fq") fchoices
  in
  let gchoices = fold_vars (function GroupChoice v -> [v] | _ -> []) in
  let fchoices = fold_vars (function FieldChoice v -> [v] | _ -> []) in
  F.fprintf fmt "win (%a) = ( %a )."
    pp_args (gchoices, fchoices)
    pp_wcond_conds wcond

(*******************************************************************)
(* \hd{Game definition} *)

type oname = string

(* \ic{A game definition consists of the adversary input,
       the definition of (named) oracles, and
       the definition of the winning condition.} *)
type gdef = {
  gdef_inputs  : rpoly list;
  gdef_oracles : (oname * odef) list;
  gdef_wcond   : wcond;
}

let pp_gdef fmt gdef =
  F.fprintf fmt "input [%a] in G.\n\n%a\n\n%a"
    (pp_list ", " RP.pp) gdef.gdef_inputs
    (pp_list "\n" (fun fmt (n,o) -> F.fprintf fmt "oracle %s%a." n pp_opoly o))
        gdef.gdef_oracles
    pp_wcond gdef.gdef_wcond