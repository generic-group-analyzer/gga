(*s Input for non-parametric problems.\\ *)

(*i*)
open Util
open Poly
(*i*)

(*******************************************************************)
(* \hd{Group settings, group elements, and assumptions (see .mli file for docs)} *)

type group_id = string

type iso = {
  iso_dom   : group_id;
  iso_codom : group_id
}

type emap = {
  em_dom   : group_id list;
  em_codom : group_id
}

type group_setting = {
  gs_isos     : iso list;
  gs_emaps     : emap list
}

type closed_group_setting = {
  cgs_isos   : iso list;
  cgs_emaps  : emap list;
  cgs_target : group_id;
  cgs_gids   : Ss.t
}

type rvar = string

module RP = MakePoly(struct
  type t = rvar
  let pp = pp_string
  let equal = (=)
  let compare = compare
end) (IntRing)

type rpoly = RP.t

let rp_to_vector mon_basis f = L.map (fun m -> RP.coeff f m) mon_basis

type group_elem = {
  ge_rpoly : rpoly;
  ge_group : group_id;
}

let shape ges = L.map (fun ge -> ge.ge_group) ges

type assumption =
  | Computational of closed_group_setting * group_elem list * group_elem
  | Decisional    of closed_group_setting * group_elem list * group_elem list

(*******************************************************************)
(* \hd{Cyclicity of group settings} *)

(* \ic{[gs_group_ids gs] returns the group ids occuring in domains and codomains in [gs].} *)
let gs_group_ids gs =
  let add_gids s l = Ss.union s (ss_of_list l) in
  let gids = L.fold_left (fun s i -> add_gids s [i.iso_codom; i.iso_dom]) Ss.empty gs.gs_isos
  in L.fold_left (fun s e -> add_gids s (e.em_codom::e.em_dom)) gids gs.gs_emaps

(* \ic{%
   [gs_iso_edges gs] returns the edges induced by the isomorphisms in [gs].
   Concretely, it returns a map [m] such that [m[i]] contains all [j]
   such that there is a $\phi : i \to j$.} *)
let gs_iso_edges gs =
  L.fold_left (fun m i -> ss_add_set i.iso_dom i.iso_codom m) Ms.empty gs.gs_isos

(* \ic{%
   [gs_emap_edges gs] returns the edges induced by the multilinear maps in [gs].
   Concretely, it returns a map [m] such that [m[i]] contains all [j]
   such that there is an $e : \ldots \times i \times \ldots \to j$.} *)
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
  let succs gid m = try Ms.find gid m with Not_found -> Ss.empty in
  let iso_edges  = gs_iso_edges gs in
  let emap_edges = gs_emap_edges gs in
  let unexplored = ref (gs_group_ids gs) in
  
  (* \ic{Start at [n] and explore reachable nodes. Keep track of
         path weight and path members.} *)
  let rec explore n path_weight path_mems =
    if Ss.mem n path_mems then (if path_weight then raise (Cyclic n))
    else (
      unexplored := Ss.remove n !unexplored;
      let path_mems = Ss.add n path_mems in
      Ss.iter (fun n -> explore n true        path_mems) (succs n emap_edges);
      Ss.iter (fun n -> explore n path_weight path_mems) (succs n iso_edges)
    )
  in

  (* \ic{Iterate [explore] for unexplored nodes until [Cyclic] is raised
     or all nodes are explored.} *)
  let rec loop () =
    if Ss.is_empty !unexplored then false
    else
      try explore (Ss.choose !unexplored) false Ss.empty; loop ()
      with Cyclic _ -> true
  in loop ()

(*******************************************************************)
(* \hd{Computation of target group} *)

(* \ic{%
   [gs_rev_iso_edges gs] returns the backwards edges induced by the
   isomorphisms and multilinear maps in [gs].
   Concretely, it returns a map [m] such that [m[j]] contains all [i]
   such that there is a $\phi : i \to j$ or $e : \ldots \times i \times \ldots \to j$.} *)
let gs_rev_edges gs =
  let m =
    L.fold_left (fun m i -> ss_add_set i.iso_codom i.iso_dom m) Ms.empty gs.gs_isos
  in
  L.fold_left
    (fun m e -> L.fold_left (fun m src -> ss_add_set e.em_codom src m) m e.em_dom)
    m
    gs.gs_emaps

(* \ic{Internal exception for [gs_find_target].} *)
exception TargetFound of group_id

(* \ic{%
   [gs_find_target gs] returns [Some(gid)] if elements from all groups
   can be moved to [gid] by applying isomorphisms and multilinear maps.
   For the multilinear maps, we assume that the adversary can get a handle
   to the group generator (polynomial $1$) in all groups.} *)
let gs_find_target gs =
  let rev_edges  = gs_rev_edges gs in
  let preds gid = try Ms.find gid rev_edges with Not_found -> Ss.empty in
  let all_gids = gs_group_ids gs in
  let reachable n =
    let visited = ref (Ss.singleton n) in
    let rec go n =
      if not (Ss.mem n !visited)
      then
        visited := Ss.add n !visited;
        Ss.iter go (preds n)
    in
    go n;
    if Ss.equal all_gids !visited then raise (TargetFound n)
  in
  try  Ss.iter (fun gid -> reachable gid) (gs_group_ids gs); None
  with TargetFound n -> Some n

(*******************************************************************)
(* \hd{Smart constructors for group settings and assumptions} *)

exception InvalidAssm of string

let fail_assm s = raise (InvalidAssm s)

let closed_generic_group gid =
  { cgs_isos  = [];
    cgs_emaps = [];
    cgs_gids  = Ss.singleton gid;
    cgs_target = gid }

let close_group_setting gs =
  if gs.gs_isos = [] && gs.gs_emaps = [] then
    fail_assm "No isomorphisms and no maps, use closed_generic_group.";
  if gs_is_cyclic gs then fail_assm "Group setting is cyclic.";
  match gs_find_target gs with
  | Some t -> 
    let gids = gs_group_ids gs in
    { cgs_isos   = gs.gs_isos;
      cgs_emaps  = gs.gs_emaps;
      cgs_gids   = gids;
      cgs_target = t }
  | None ->
    fail_assm "No target group"

let ensure_valid_groups cgs ges =
  if (List.exists (fun ge -> not (Ss.mem ge.ge_group cgs.cgs_gids)) ges)
  then fail_assm "Assumption contains elements in invalid group"

let ensure_equal_shape left right =
  if shape left <> shape right then fail_assm "assumptions do not have the same shape"

let standardize_ones cgs inp =
  let inp = L.filter (fun ge -> not (RP.equal RP.one ge.ge_rpoly)) inp in
  let ones   =
    L.map
      (fun gid -> { ge_group = gid; ge_rpoly = RP.one })
      (Ss.elements cgs.cgs_gids |> L.sort compare)
  in
  ones @ inp

let mk_computational cgs inputs chal =
  let inputs = standardize_ones cgs inputs in
  ensure_valid_groups cgs (chal::inputs);
  Computational(cgs,inputs,chal)

let mk_decisional cgs inputs_left inputs_right =
  let inputs_left = standardize_ones cgs inputs_left in
  let inputs_right = standardize_ones cgs inputs_right in
  ensure_valid_groups cgs (inputs_left@inputs_right);
  ensure_equal_shape inputs_left inputs_right;
  Decisional(cgs,inputs_left,inputs_right)

(*i*)
(*******************************************************************)
(* \hd{Pretty printing} *)

let pp_iso fmt i = F.fprintf fmt "phi : %s -> %s" i.iso_dom i.iso_codom

let pp_emap fmt e =
  F.fprintf fmt "e : %a -> %s" (pp_list " x " pp_string) e.em_dom e.em_codom

let pp_iso_s fmt i = F.fprintf fmt "phi_%s,%s" i.iso_dom i.iso_codom

let pp_emap_s fmt e =
  F.fprintf fmt "e_%s" e.em_codom

let pp_group_id fmt gid =
  F.fprintf fmt "G_%s" gid

let pp_group_elem fmt ge =
  F.fprintf fmt "%a : %a" RP.pp ge.ge_rpoly pp_group_id ge.ge_group

let pp_gs fmt gs =
  F.fprintf fmt "group setting:\n  %a\n  %a\n"
    (pp_list "\n  " pp_iso) gs.gs_isos
    (pp_list "\n  " pp_emap) gs.gs_emaps
(*i*)

(*i*)
(*******************************************************************)
(* \hd{Internals for testing} *)

module Internals = struct
  let gs_is_cyclic = gs_is_cyclic
end
(*i*)

