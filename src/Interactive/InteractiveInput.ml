(*s Input for interactive assumptions. *)
(*i*)
open Util
open LPoly
open LStringPoly
(*i*)

exception InvalidAssumption of string

(*******************************************************************)
(* \hd{Identifiers, types, and group settings} *)

(* \ic{Identifier for variables and parameters.} *)
type id = string

(* \ic{Group identifier.} *)
type gid = string

(* \ic{A type is either a field element or a (handle to) a group element.} *)
type ty = Field | Group of gid

(* \ic{Return [gid]s occuring in [ty].} *)
let gids_in_ty ty =
  match ty with
  | Group gid -> [gid]
  | _         -> []

(* \ic{Typed identifier.} *)
type tid = {
  tid_id : id;
  tid_ty : ty;
}

(* \ic{Return true if tid has [Field] type.} *)
let is_field_tid tid =
  tid.tid_ty = Field

(* \ic{Return true if tid has [Group] type.} *)
let is_group_tid tid =
  match tid.tid_ty with
  | Group _ -> true
  | _       -> false

(* \ic{Return [gid]s occuring in [tid].} *)
let gids_in_tid tid = gids_in_ty tid.tid_ty

(* \ic{An isomorphism has a domain and a codomain.} *)
type iso = {
  iso_dom   : gid;
  iso_codom : gid
}

(* \ic{An n-linear map has a domain and a codomain.} *)
type emap = {
  em_dom   : gid list;
  em_codom : gid
}

(* \ic{A group setting defines a list of isomorphisms and a list of n-linear maps} *)
type group_setting = {
  gs_isos      : iso list;
  gs_emaps     : emap list;
}

let gids_in_gs gs =
       (conc_map (fun iso -> [iso.iso_codom; iso.iso_dom]) gs.gs_isos)
     @ (conc_map (fun em -> em.em_codom::em.em_dom) gs.gs_emaps)
  |> sorted_nub compare

(*i*)
let pp_ty fmt ty = match ty with
  | Field   -> pp_string fmt "Fq"
  | Group s -> F.fprintf fmt "G%s" s

let pp_tid fmt tid =
  F.fprintf fmt "%s:%a" tid.tid_id pp_ty tid.tid_ty

let pp_iso fmt i = F.fprintf fmt "phi : %s -> %s" i.iso_dom i.iso_codom

let pp_emap fmt e =
  F.fprintf fmt "e : %a -> %s" (pp_list " * " pp_string) e.em_dom e.em_codom

let pp_iso_s fmt i = F.fprintf fmt "phi_%s,%s" i.iso_dom i.iso_codom

let pp_emap_s fmt e =
  F.fprintf fmt "e_%s" e.em_codom

let pp_group_id fmt gid =
  F.fprintf fmt "G_%s" gid

let pp_gs fmt gs =
  F.fprintf fmt "group setting:\n  %a\n  %a\n"
    (pp_list "\n  " pp_iso) gs.gs_isos
    (pp_list "\n  " pp_emap) gs.gs_emaps

(*i*)


(*******************************************************************)
(* \hd{Adversary input definition} *)

(* \ic{For the adversary input, we use polynomials in $\ZZ[\vec{X}]$
       for random variables $\vec{X}$ represented by strings.} *)

module RP = SP

type rpoly = RP.t

(*******************************************************************)
(* \hd{Oracle definition} *)

(* \ic{Variables in oracle polynomials are either oracle parameters (field
      elements or handles), shared random variables sampled before calling the
      adversary, or variables sampled in the oracle.} *)
type ovar = 
  | Param  of tid
  | SRVar  of id
  | ORVar  of id

(* \ic{Return all [gid]s occuring in [ov].} *)
let gids_in_ovar ov =
  match ov with
  | Param tid -> gids_in_tid tid
  | _         -> []


(*i*)
let string_of_ovar v = match v with
  | Param i -> i.tid_id
  | SRVar s | ORVar s -> s

let pp_ovar fmt v = pp_string fmt (string_of_ovar v)
(*i*)

(* \ic{Oracle polynomials.} *)
module OP = MakePoly(struct
  type t = ovar
  let pp = pp_ovar
  let equal = (=)
  let compare = compare
end) (IntRing)

type opoly = OP.t

type oname = string

(* \ic{An oracle definition consists of an oracle name and a list of
       oracle polynomials together with the group in which the
       value is returned. The oracle $on$ for $(f_1,\group_{j_1}),\ldots,(f_n,\group_{j_n})$
       is then defined as follows:
       \begin{enumerate}
       \item Take parameters
         $(m_1 : \field,\ldots,m_{l}:\field,h_1:\group_{i_1},\ldots, h_{k}:\group_{i_k})$
         for all (typed) parameters that occur in $\vec{f}$.
       \item Sample random values $A_i \in \field$ for all oracle random variables
         that occur in $\vec{f}$.
       \item Return handles $\tilde{h}_1,\ldots,\tilde{h}_n$ to values
        $v_i = f_i(\vec{X},\vec{A},\vec{m},L_{i_1,h_1},\ldots,L_{i_k,h_k})$ for
        $i \in [n]$.
       \end{enumerate}} *)
type odef = {
  odef_name   : oname;
  odef_return : (opoly * gid) list;
}

let gids_in_odef odef =
       (L.map snd odef.odef_return)
     @ (conc_map gids_in_ovar (conc_map (OP.vars % fst) odef.odef_return))
  |> sorted_nub compare

(*i*)
let pp_opoly fmt opolys_group =
  let opolys = L.map fst opolys_group in
  let get_param v = match v with Param i -> [i] | _ -> [] in
  let get_orvar v = match v with ORVar i -> [i] | _ -> [] in
  let params =
    conc_map (fun f -> conc_map get_param (OP.vars f)) opolys
    |> sorted_nub compare
  in
  let orvars =
    conc_map (fun f -> conc_map get_orvar (OP.vars f)) opolys
    |> sorted_nub compare
  in
  let pp_opoly_group fmt (op,gid) =
    F.fprintf fmt "%a in %a" OP.pp op pp_ty (Group gid)
  in
  F.fprintf fmt "(%a) = %a; return (%a)"
    (pp_list ", " (fun fmt -> pp_tid fmt)) params
    (pp_list "; " (fun fmt -> F.fprintf fmt "sample %s")) orvars
    (pp_list ", " pp_opoly_group) opolys_group

let pp_odef fmt od =
  F.fprintf fmt "oracle %s%a." od.odef_name pp_opoly od.odef_return

(*i*)

(*******************************************************************)
(* \hd{Winning condition definition} *)

(*i \ic{A winning condition is given by two sets of polynomials,
   one set that is interpreted as the required equalities and one set
   interpreted as the required inequalities.
   These polynomials are in $\ZZ[\vec{X},\vec{U},\vec{w},\vec{m},\vec{h}]$
   where $\vec{X}$ denotes the random variables, $\vec{U}$ denotes the
   adversary choices in $\group$, $\vec{w}$ denotes the adversary choices
   in $\field$, and $\vec{m}$ denotes the oracle arguments in $\field$,
   and $\vec{h}$ denotes the oracle arguments in $\group$.
   Every (in)equality (resp. equality) polynomial containing oracle argument
   variables~$m$ (or $h$) is interpreted as
   $\forall i \in [q]: f(\ldots,m_i,\ldots) \neq 0$ (resp. $=$).} i*)

(* \ic{Variables in winning condition polynomials ar either (shared)
       random variables, oracle parameters (field elements or handles),
       or values chosen by the adversary for the winning condition
       (field elements or handles).} *)
type wvar = 
  | RVar   of id
  | OParam of tid
  | Choice of tid

(* \ic{Return [gid]s in [wv].} *)
let gids_in_wvar wv =
  match wv with
  | Choice tid | OParam tid -> gids_in_tid tid
  | RVar _                  -> []

(*i*)
let string_of_wvar v = match v with
  | Choice i -> i.tid_id
  | RVar s   -> s
  | OParam i -> i.tid_id ^"_i"

let pp_wvar fmt v = pp_string fmt (string_of_wvar v)
(*i*)

(* \ic{Winning condition polynomials.} *)
module WP = MakePoly(struct
  type t = wvar
  let pp = pp_wvar
  let equal = (=)
  let compare = compare
end) (IntRing)

type wpoly = WP.t

(*i*)
let pp_wpoly fmt wp =
  if L.exists (function OParam _ -> true | _ -> false) (WP.vars wp) then
    F.fprintf fmt "forall i: %a" WP.pp wp
  else
    WP.pp fmt wp
(*i*)

(* \ic{A winning condition consists of a list of equalities and a list
       of inequalities. Here, winning condition polynomials are evaluated
       as follows:
       \begin{itemize}
       \item Shared random variables $X$ are replaced by the corresponding values
         in $\field$.
       \item Adversary choices $w \in \field$ are used directly.
       \item Adversary choices in $h$ for $\group_i$ are replaced by the
         values referenced by the corresponding handle.
       \item Polynomials containing oracle parameters
          $m \in \field$ are interpreted as
          $\forall i \in [q].\, f(\ldots,m_i,\ldots) = 0$ (or $\neq$).
       \item Polynomials containing oracle parameters
          $h$ for $\group_j$ are interpreted as
          $\forall i \in [q].\, f(\ldots,L_{j,h_i},\ldots) = 0$.
       \end{itemize}
       } *) 
type wcond = {
  wcond_eqs   : wpoly list;
  wcond_ineqs : wpoly list;
}

(*i*)
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
  let choices = fold_vars (function Choice tid -> [tid] | _ -> []) in
  F.fprintf fmt "win (%a) = ( %a )." (pp_list ", " pp_tid) choices pp_wcond_conds wcond
(*i*)

(*******************************************************************)
(* \hd{Game definition} *)

(* \ic{A game definition consists of the adversary input,
       the definition of (named) oracles, and
       the definition of the winning condition.} *)
type gdef = {
  gdef_gs     : group_setting;
  gdef_inputs : (rpoly * gid) list;
  gdef_odefs  : odef list;
  gdef_wcond  : wcond;
}

(* \ic{Return all [gids] occuring in game definition} *)
let gids_in_gdef gdef =
  let wpolys = gdef.gdef_wcond.wcond_eqs @ gdef.gdef_wcond.wcond_ineqs in
       (gids_in_gs gdef.gdef_gs)
     @ (L.map snd gdef.gdef_inputs)
     @ (conc_map gids_in_odef gdef.gdef_odefs)
     @ (conc_map gids_in_wvar (conc_map WP.vars wpolys))
  |> sorted_nub compare

(* \ic{Simplify game definition by removing oracle outputs that are redundant
       because they can be computed from the oracle inputs and other outputs.
       For example in $o(x) = return\; [A,A*x]\; in\; \group_1$, $A*x$ is
       redundant.} *)

let simp_gdef gdef = gdef (*i
  let is_fparam = function Param(tid) when is_field_tid tid -> true | _ -> false in
  let rec only_fparams_missing xs ys =
    match xs,ys with
    | [], _ ->
      L.for_all is_fparam ys
    | x::xs, y::ys when x = y ->
      only_fparams_missing xs ys
    | xs, y::ys when is_fparam y ->
      only_fparams_missing xs ys
    | _ ->
      false
  in
  let computable_from (k,kgid) (s,sgid) =
    match OP.to_terms k, OP.to_terms s with
    | [(vks,ck)],[(vss,_cs)]
      when kgid = sgid && not (IntRing.equal ck IntRing.zero) ->
      only_fparams_missing (L.sort compare vks) (L.sort compare vss)
    | _ -> false
  in
  let rec simp_orcl ls rs =
    match rs with
    | []    -> L.rev ls
    | r::rs ->
      if L.exists (fun l -> computable_from l r) ls
      then simp_orcl ls rs
      else simp_orcl (r::ls) rs
  in
  let simp_odef od =
    { od with odef_return = simp_orcl [] od.odef_return }
  in
  { gdef with gdef_odefs = List.map simp_odef gdef.gdef_odefs }
i*)

(* \ic{Group elements chosen by adversary for winning condition.} *)
let gchoices_of_gdef gdef =
  let eqs = gdef.gdef_wcond.wcond_eqs in
  let ineqs = gdef.gdef_wcond.wcond_ineqs in  
  conc_map WP.vars (eqs@ineqs)
  |> L.map (function Choice(tid) when is_group_tid tid -> Some(tid) | _ -> None)
  |> catSome
  |> sorted_nub compare


(*i*)
let pp_gdef fmt gdef =
  F.fprintf fmt "%a\ninput [%a].\n\n%a\n\n%a"
    pp_gs gdef.gdef_gs
    (pp_list ", " (fun fmt (p,gid) -> F.fprintf fmt "%a in %s" RP.pp p gid)) gdef.gdef_inputs
    (pp_list "\n" pp_odef) gdef.gdef_odefs
    pp_wcond gdef.gdef_wcond
(*i*)
