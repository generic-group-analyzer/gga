(*s Input for non-parametric problems.\\ *)

(*i*)
open Util
open Poly
(*i*)

(*******************************************************************)
(* \hd{Group settings, group elements, and assumptions} *)

(* \ic{Each group has an identifier.} *)
type group_id = string

(* \ic{An isomorphism has a domain and a codomain.} *)
type iso = {
  iso_dom   : group_id;
  iso_codom : group_id
}

(* \ic{A multi-linear map has a domain and a codomain.} *)
type emap = {
  em_dom   : group_id list;
  em_codom : group_id
}

(* \ic{%
   A group setting consists of isomorphisms,
   and multilinear maps. We keep the group ids
   implicit.} *)
type group_setting = {
  gs_isos     : iso list;
  gs_emaps     : emap list
}

(* \ic{We use strings for random variables such as $X$. } *)
type rvar = string

(* \ic{Random polyomials such as $X*X + Y$.} *)
module RP = MakePoly(struct
  type t = rvar
  let pp = pp_string
  let equal = (=)
  let compare = compare
end) (IntRing)

type rpoly = RP.t

(* \ic{We model a group element as a random polynomial and a group identifier.} *)
type group_elem = {
  ge_rpoly : rpoly;
  ge_group : group_id;
}

(* \ic{%
   A non-parametric \emph{computational assumption} consists of the group setting,
   the list of adversary inputs, and the challenge.
   A non-parametric \emph{decisional assumption} consists of the group setting,
   the left adversary input, and the right adversary input.} *)
type assumption =
  | Computational of group_setting * group_elem list * rpoly
  | Decisional    of group_setting * group_elem list * rpoly list

(*******************************************************************)
(* \hd{Cyclicity of group settings} *)

(* \ic{[gs_group_ids gs] returns the group ids occuring in domains or codomains in [gs].} *)
let gs_group_ids gs =
  let gids =
    L.fold_left
      (fun acc i -> Ss.add i.iso_codom (Ss.add i.iso_dom acc))
      Ss.empty
      gs.gs_isos
  in
  L.fold_left
    (fun acc e -> Ss.union (ss_of_list e.em_dom) (Ss.add e.em_codom acc))
    gids
    gs.gs_emaps

(* \ic{[gs_iso_edges gs] returns the edges induced by the isomorphisms in [gs].} *)
let gs_iso_edges gs =
  L.fold_left (fun m i -> ss_add_set i.iso_dom i.iso_codom m) Ms.empty gs.gs_isos


(* \ic{[gs_emap_edges gs] returns the edges induced by the multilinear maps in [gs].} *)
let gs_emap_edges gs =
  L.fold_left
    (fun m e -> L.fold_left (fun m src -> ss_add_set src e.em_codom m) m e.em_dom)
    Ms.empty
    gs.gs_emaps

(* \ic{Internal exception for [gs_is_cyclic].} *)
exception Cyclic of group_id

(* \ic{%
   [gs_is_cyclic gs] returns [true] if the group setting has
   a cycle that allows for an unbounded number of mutiplications.
   More precisely, consider the weighted graph with group ids $i$ as
   vertices and edges $i \mapsto i'$ of weight zero for all isomorphisms
   $\phi: i \to i'$ and edges $i_1 \mapsto i',\ldots, i_k \mapsto i'$ with weight
   one for all multilinear maps $e : i_1 \times \ldots \times i_k \to i'$.
   The group setting is cyclic iff the graph has a cycle with non-zero
   weight.} *)
let gs_is_cyclic gs =
  let iso_edges  = gs_iso_edges gs in
  let emap_edges = gs_emap_edges gs in
  let succs k m = try Ms.find k m with Not_found -> Ss.empty in
  let rec explore cur_id weight visited =
    if Ss.mem cur_id visited then (
      if weight then raise (Cyclic cur_id) else ()
    ) else (
      let visited = Ss.add cur_id visited in
      Ss.iter (fun id -> explore id true   visited) (succs cur_id emap_edges);
      Ss.iter (fun id -> explore id weight visited) (succs cur_id iso_edges);
    )
  in
  try
    Ss.iter
      (fun id -> explore id false Ss.empty)
      (gs_group_ids gs);
    false
  with
    Cyclic _ -> true

(*******************************************************************)
(* \hd{Predefined group settings} *)

let gs_bilinear_asym = {
  gs_isos = [{ iso_dom = "1"; iso_codom = "2"}];
  gs_emaps = [{ em_dom = ["1";"2"]; em_codom = "1:2"}];
}

let gs_bilinear_sym = {
  gs_isos = [];
  gs_emaps = [{ em_dom = ["1";"1"]; em_codom = "2"}];
}

(*i*)
(*******************************************************************)
(* \hd{Pretty printing} *)

let pp_iso fmt i = F.fprintf fmt "phi : %s -> %s" i.iso_dom i.iso_codom

let pp_emap fmt e =
  F.fprintf fmt "e : %a -> %s" (pp_list " x " pp_string) e.em_dom e.em_codom

let pp_iso_s fmt i = F.fprintf fmt "phi_%s,%s" i.iso_dom i.iso_codom

let pp_emap_s fmt e =
  F.fprintf fmt "e_%s" e.em_codom

let pp_group_elem fmt ge =
  F.fprintf fmt "%a @@ %s" RP.pp ge.ge_rpoly ge.ge_group

let pp_gs fmt gs =
  F.fprintf fmt "group setting:\n  %a\n  %a\n"
    (pp_list "\n  " pp_iso) gs.gs_isos
    (pp_list "\n  " pp_emap) gs.gs_emaps
(*i*)
