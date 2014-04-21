open Util
open Poly
open NonParamInput

(*******************************************************************)
(* \hd{Recipes and recipe polynomials} *)

(* \ic{A recipe describes how to compute a term from a list of inputs.
   [Param(i)] stands for taking the $i$-th element,
   [Iso(i,r)] stands for computing $r$ and then applying the isomorphism $i$, and
   [Emap(e,rs)] stands for computing $rs$ and then applying the map $e$.} *)
type recipe =
  | Param of int
  | Iso   of iso * recipe
  | Emap  of emap * recipe list

(* \ic{Apply a recipe to a list of inputs.} *)
let apply_recipe recip0 inputs =
  let rec go recip =
    match recip with
    | Param i        -> (L.nth inputs i).ge_rpoly
    | Emap(_,recips) -> RP.lmult (L.map go recips)
    | Iso(_,recip)   -> go recip
  in
  go recip0

(* \ic{Recipe polyomials such as $W_1*W_2 + W_3$.} *)
module ReP = MakePoly(struct
  type t = int
  let pp = pp_int
  let equal = (=)
  let compare = compare
end) (IntRing)

(* \ic{Operations required for completion.} *)
type completion_ops = (group_id * recipe)

(* \ic{Apply completion ops to a list of inputs.
   Not that the cops also includes recipes for all elements
   of inputs.} *)
let apply_completion_ops inputs cops =
  let compute_group_elem (gid,recip) =
    {ge_rpoly = apply_recipe recip inputs; ge_group = gid }
  in
  L.map compute_group_elem cops

(* \ic{Sets of recipe polynomials. Different recipes can correspond to the
   same recipe polynomial.} *)
module Srep = Set.Make(struct
  type t = ReP.t
  let compare = ReP.compare
end)

(* \ic{Convert list of recipe polynomials to set of recipe polynomials.} *)
let srep_of_list = L.fold_left (fun acc x -> Srep.add x acc) Srep.empty

let srep_add_set = add_set Srep.empty Srep.add

(* \ic{Map with pairs of group ids and recipe polynomials as keys.} *)
module Mrep = Map.Make(struct
  type t = group_id * ReP.t
  let compare (gid1,f1) (gid2,f2) =
    let d = compare gid1 gid2 in
    if d <> 0 then d else ReP.compare f1 f2
end)

(*******************************************************************)
(* \hd{Computation of completion operations} *)

(* \ic{[completion_ops gs inp_type] computes a
   sufficient set of isomorphism and multilinear map
   applications with respect to the group setting [gs]
   and an input list with group ids [inp_gids].} *)
let completion_ops gs inp_gids =

  (* \ic{We keep a map from group ids to known recipe polynomials.} *)
  let m_known = ref Ms.empty in
  let find_known gid = try Ms.find gid !m_known with Not_found -> Srep.empty in

  (* \ic{We keep a map from known recipe polynomials to their recipes.} *)

  let m_recipes = ref Mrep.empty in
  let find_recipe gid rp = Mrep.find (gid,rp) !m_recipes in

  (* \ic{The [add] function adds a recipe polynomial if it is new.
     It uses the [changed] variable to track changes to [m_known].} *)

  let changed = ref false in
  let add (rp : ReP.t) (recipe : recipe) (gid : string) =
    let known = find_known gid in
    if Srep.mem rp known then ()
    else (
      changed := true;
      m_known := srep_add_set gid rp !m_known;
      m_recipes := Mrep.add (gid,rp) recipe !m_recipes
    )
  in

  (* \ic{ We first add all inputs polynomial $W_i$ with recipe $W_i$. } *)
  List.iter
    (fun (i,gid) -> add (ReP.var i) (Param i) gid)
    (L.mapi (fun i gid -> (i,gid)) inp_gids);

  (* \ic{We then use the following loop.} *)
  let rec loop () =
    changed := false;

    (* \ic{We loop over all $\phi: i \to i'$, for all
       $g \in$ [m_known[i]] with recipe $\zeta$, we add $g$ to
       [m_known[i']] with recipe $\phi(\zeta)$.} *)

    List.iter
      (fun i ->
         let gid, gid' = i.iso_dom, i.iso_codom in
         Srep.iter
           (fun rp -> add rp (Iso(i,find_recipe gid rp)) gid')
           (find_known gid))
      gs.gs_isos;

    (* \ic{We loop over all $e: i_1 \times \ldots \times i_k \to i'$,
       for all
       $(g_1,\ldots,g_k) \in$ [m_known[i_1]] $\times \ldots \times$ [m_known[i_k]]
       with recipe $(\zeta_1,\ldots,\zeta_k)$, we add $g_1 * \ldots * g_k$ to
       [m_known[i']] with recipe $e(\zeta_1,\ldots,\zeta_k)$.} *)

    List.iter
      (fun e ->
         let gids, gid' = e.em_dom, e.em_codom in
         let known_rps = L.map (fun gid -> Srep.elements (find_known gid)) gids in
         List.iter
           (fun rps ->
              let recips = L.map2 (fun gid rp -> find_recipe gid rp) gids rps in
              add (ReP.lmult rps) (Emap(e,recips)) gid')
           (cart_prod known_rps))
      gs.gs_emaps;
  
    (* \ic{If nothing changed, we return a list of recipes and group ids.
       Otherwise, we loop again.} *)
    
    if !changed then loop ()
    else conc_map
           (fun (gid,rps) -> L.map (fun rp -> (gid, find_recipe gid rp)) (Srep.elements rps))
           (Ms.bindings !m_known)
  in
  loop ()

(*i*)
(*******************************************************************)
(* \hd{Pretty printing} *)

let rec pp_recipe fmt c =
  match c with
  | Param(i)  -> F.fprintf fmt "W_%i" i
  | Iso(iso, c)  -> F.fprintf fmt "%a(%a)" pp_iso_s iso pp_recipe c
  | Emap(em, cs) -> F.fprintf fmt "%a(%a)" pp_emap_s em (pp_list "," pp_recipe) cs

(*i*)

let check () =
  let inputs =
    [ { ge_rpoly = RP.var "X"; ge_group = "1" }
    ; { ge_rpoly = RP.var "Y"; ge_group = "1" }
    ; { ge_rpoly = RP.var "Z"; ge_group = "2" }
    ; { ge_rpoly = RP.var "U"; ge_group = "1:2" }
    ]
  in
  let input_groups = L.map (fun ge -> ge.ge_group) inputs in
  let cops = completion_ops gs_bilinear_asym input_groups in
  F.printf "completion_ops:\n%a\n"
    (pp_list "\n" (fun fmt (gid,r)-> F.fprintf fmt "%a @@ %s" pp_recipe r gid))
    cops;
  let known = apply_completion_ops inputs cops in
  F.printf "\ncompletion:\n%a" (pp_list "\n" pp_group_elem) known;
  exit 0
