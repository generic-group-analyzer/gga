(*i*)
open Util
open Poly
open NonParamInput
(*i*)

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

let lmult_rp_vect gs rpss =
  L.fold_left
    (fun acc rps -> L.map (fun (f,g) -> RP.mult f g) (L.combine acc rps))
    (replicate RP.one gs.cgs_prime_num)
    rpss

(* \ic{Apply a recipe to a list of inputs.\\
   {\bf Composite:} Multiply component-wise} *)
let apply_recipe gs inputs recip0 =
  let rec go recip : rpoly list =
    match recip with
    | Param i        -> (L.nth inputs i).ge_rpoly
    | Emap(_,recips) ->
      let rpss = L.map go recips in
      lmult_rp_vect gs rpss
    | Iso(_,recip)   -> go recip
  in
  go recip0

(* \ic{Recipe polynomials such as $W_1*W_2 + W_3$, Different recipes can correspond
   to the same recipe polynomial.} *)
module ReP = MakePoly(struct
  type t = int
  let pp = pp_int
  let equal = (=)
  let compare = compare
end) (IntRing)

(* \ic{[apply_completion_ops cops inputs] applies completion ops [cops] to [inputs].} *)
let apply_completion_ops gs cops inputs =
  L.map (apply_recipe gs inputs) cops

(* \ic{Sets of recipe polynomials. } *)
module Srep = Set.Make(struct type t = ReP.t let compare = ReP.compare end)

(* \ic{[srep_add_set k v m] adds [v] to the set stored under key [k] in [m].} *) 
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

(* \ic{[completion_ops gs cgid inp_type] computes a
   sufficient set of isomorphism and multilinear map
   applications with respect to the group setting [gs]
   and an input list with group ids [inp_gids]
   such that all computable elements in [cgid]
   can be computed by first applying these operations
   followed only by [add] and [neg].\\
    {\bf Composite:} Nothing changes, the param variables stand for tuples now.} *)
let completion_ops cgs cgid inp_gids =

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

  (* \ic{ We first add all input polynomials $W_i$ with recipe $W_i$.
     For the first entries corresponding to $1$, we use the input polynomial $1$.} *)
  let first_non_one = Ss.cardinal cgs.cgs_gids in
  L.iter
    (fun (i,gid) -> add (if i < first_non_one then ReP.one else ReP.var i) (Param i) gid)
    (L.mapi (fun i gid -> (i,gid)) inp_gids);

  (* \ic{We then use the following loop for completion:} *)
  let rec complete () =
    changed := false;

    (* \ic{We loop over all $\phi: i \to i'$, for all
       $g \in$ [m_known[i]] with recipe $\zeta$, we add $g$ to
       [m_known[i']] with recipe $\phi(\zeta)$.} *)
    L.iter
      (fun i ->
         let gid, gid' = i.iso_dom, i.iso_codom in
         Srep.iter
           (fun rp -> add rp (Iso(i,find_recipe gid rp)) gid')
           (find_known gid))
      cgs.cgs_isos;

    (* \ic{We loop over all $e: i_1 \times \ldots \times i_k \to i'$,
       for all
       $(g_1,\ldots,g_k) \in$ [m_known[i_1]] $\times \ldots \times$ [m_known[i_k]]
       with recipe $(\zeta_1,\ldots,\zeta_k)$, we add $g_1 * \ldots * g_k$ to
       [m_known[i']] with recipe $e(\zeta_1,\ldots,\zeta_k)$.} *)
    L.iter
      (fun e ->
         let gids, gid' = e.em_dom, e.em_codom in
         let known_rps = L.map (fun gid -> Srep.elements (find_known gid)) gids in
         L.iter
           (fun rps ->
              let recips = L.map2 (fun gid rp -> find_recipe gid rp) gids rps in
              add (ReP.lmult rps) (Emap(e,recips)) gid')
           (cart_prod known_rps))
      cgs.cgs_emaps;
  
    (* \ic{If nothing changed, we return a list of recipes and group ids.
       Otherwise, we loop again.} *)
    if !changed then complete ()
    else L.map
           (fun rp -> find_recipe cgid rp)
           (Srep.elements (Ms.find cgid !m_known))
  in
  complete ()

let completion_for_group gs cgid inputs =
  let cops = completion_ops gs cgid (shape inputs) in
  (apply_completion_ops gs cops inputs, cops)

let completions_for_group gs cgid linputs rinputs =
  assert (shape linputs = shape rinputs);
  let cops = completion_ops gs cgid (shape linputs) in
  ( apply_completion_ops gs cops linputs
  , apply_completion_ops gs cops rinputs
  , cops)

(*i*)
(*******************************************************************)
(* \hd{Pretty printing} *)

let rec pp_recipe fmt c =
  match c with
  | Param(i)     -> F.fprintf fmt "h_%i" i
  | Iso(iso, c)  -> F.fprintf fmt "%a(%a)" pp_iso_s iso pp_recipe c
  | Emap(em, cs) -> F.fprintf fmt "%a(%a)" pp_emap_s em (pp_list "," pp_recipe) cs

(*i*)