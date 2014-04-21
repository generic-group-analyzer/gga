open Util
open Poly
open NonParamInput

type recipe =
  | Param of int
  | Iso   of iso * recipe
  | Emap  of emap * recipe list

(* \ic{Recipe polyomials such as $W_1*W_2 + W_3$.} *)
module RP = MakePoly(struct
  type t = int
  let pp = pp_int
  let equal = (=)
  let compare = compare
end) (IntRing)

(* \ic{Sets of recipe polynomials. Different recipes can correspond to the
   same recipe polynomial.} *)
module Srp = Set.Make(struct
  type t = RP.t
  let compare = RP.compare
end)

(* \ic{Convert list of recipe polynomials to set of recipe polynomials.} *)
let srp_of_list = L.fold_left (fun acc x -> Srp.add x acc) Srp.empty

let srp_add_set = add_set Srp.empty Srp.add

(* \ic{Map with pairs of group ids and recipe polynomials as keys.} *)
module Mrp = Map.Make(struct
  type t = group_id * RP.t
  let compare (gid1,f1) (gid2,f2) =
    let d = compare gid1 gid2 in
    if d <> 0 then d else RP.compare f1 f2
end)

(* \ic{[sufficient_isoms_emaps gs inp_type] computes a
   sufficient set of isomorphism and multilinear map
   applications with respect to the group setting [gs]
   and an input list with group ids [inp_gids].} *)
let sufficient_isoms_emaps gs inp_gids =

  (* \ic{We keep a map from group ids to known recipe polynomials.} *)
  let m_known = ref Ms.empty in
  let find_known gid = try Ms.find gid !m_known with Not_found -> Srp.empty in

  (* \ic{We keep a map from known recipe polynomials to their recipes.} *)

  let m_recipes = ref Mrp.empty in
  let find_recipe gid rp = Mrp.find (gid,rp) !m_recipes in

  (* \ic{The [add] function adds a recipe polynomial if it is new.
     It uses the [changed] variable to track changes to [m_rps].} *)

  let changed = ref false in
  let add (rp : RP.t) (recipe : recipe) (gid : string) =
    let known = find_known gid in
    if Srp.mem rp known then ()
    else (
      changed := true;
      m_known := srp_add_set gid rp !m_known;
      m_recipes := Mrp.add (gid,rp) recipe !m_recipes
    )
  in

  (* \ic{ We first add all inputs polynomial $W_i$ with recipe $W_i$. } *)
  List.iter
    (fun (i,gid) -> add (RP.var i) (Param i) gid)
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
         Srp.iter
           (fun rp -> add rp (Iso(i,find_recipe gid rp)) gid')
           (find_known gid))
      gs.gs_isos;

    (* \ic{We loop over all $e: i_1 \times \ldots \times i_k \to i'$,
       for all
       $(g_1,\ldots,g_k) \in$ [m_known[i_1]] $\times \ldots \times$ [m_known[i_k]]
       with recipes $\zeta_1,\ldots,\zeta_k$, we add $g_1 * \ldots * g_k$ to
       [m_known[i']] with recipe $e(\zeta_1,\ldots,\zeta_k)$.} *)

    (* FIXME *)


    (* \ic{If nothing changed, we return a list of recipes and group ids.
       Otherwise, we loop again.} *)
    
    if !changed
    then loop ()
    else conc_map
           (fun (gid,rps) -> L.map (fun rp -> (gid, find_recipe gid rp)) (Srp.elements rps))
           (Ms.bindings !m_known)
  in
  loop ()

(*i*)
(*******************************************************************)
(* \hd{Pretty printing} *)

let rec pp_recipe fmt c =
  match c with
  | Param(i)  -> F.fprintf fmt "W_%i" i
  | Iso(iso, c)  -> F.fprintf fmt "(%a)(%a)" pp_iso iso pp_recipe c
  | Emap(em, cs) -> F.fprintf fmt "(%a)(%a)" pp_emap em (pp_list "," pp_recipe) cs

(*i*)

let check () =
  let required = sufficient_isoms_emaps gs_bilinear_asym ["1";"1";"2";"1:2"] in
  F.printf "check:\n%a"
    (pp_list "\n" (fun fmt (gid,r)-> F.fprintf fmt "%a @@ %s" pp_recipe r gid))
    required;
  exit 0
