(*s This module provides module types [Var] for variables and [Ring] for
    rings. These types are used to define the [MakePoly] functor that defines
    a polynomial module. We also define [IntRing]. *)
(*i*)
open Util
open PolyInterfaces
(*i*)


module IntRing = struct
  type t = int
  let pp fmt i = F.fprintf fmt "%i" i

  let add = (+)
  let opp a = - a
  let mult a b = a * b
  let one = 1
  let zero = 0
  let ladd cs = L.fold_left (fun acc c -> c + acc) zero cs
end

(* \ic{
   We assume that polymorphic equality and comparison
   makes sense for V.t and C.t.} *)
module MakePoly (V : Var) (C : Ring) = struct
  type coeff = C.t
  type var   = V.t

  (* \ic{
     We represent polynomials as assoc lists from
     monomials to coefficents. See [norm] for invariants
     that we maintain.} *)
  type monom = V.t list

  type term = monom * C.t

  type t = term list

  (*i*)
  (*********************************************************************)
  (* \ic{\bf Pretty printing} *)

  let pp_monom fmt m =
    F.fprintf fmt "%a" (pp_list "*" V.pp) m

  let pp_term fmt (m,c) =
    if m = [] then F.fprintf fmt "%a" C.pp c
    else if c = C.one then pp_monom fmt m
    else F.fprintf fmt "%a*%a" C.pp c pp_monom m

  let pp fmt f =
    match f with
    | [] -> F.fprintf fmt "0"
    | _  -> F.fprintf fmt "%a" (pp_list " + " pp_term) f
  (*i*)

  (*********************************************************************)
  (* \ic{\bf Internal functions} *)

  (* \ic{The [norm] function ensures that:
     \begin{itemize}
     \item Each monomial is sorted.
     \item Each monomial with non-zero coefficient has exactly one entry.
     \item The list is sorted by the monomials (keys).
     \end{itemize} }*)
  let norm f =
    f |> L.map (fun (m,c) -> (L.sort compare m, c))
      |> L.sort (fun (m1,_c1) (m2,_c2) -> compare m1 m2)
      |> group (fun (m1,_) (m2,_) -> m1 = m2)
      |> L.map (fun ys -> (fst (L.hd ys), C.ladd (L.map snd ys)))
      |> L.filter (fun (_,c) -> c <> C.zero)

  let mult_term_poly (m,c) f =
    L.map (fun (m',c') -> (L.sort compare (m @ m')), C.mult c c') f

  (*********************************************************************)
  (* \ic{\bf Ring operations on polynomials} *)

  let add f g = norm (f @ g)

  (* \ic{No [norm] required since the keys (monomials) are unchanged.} *)
  let opp f = L.map (fun (m,c) -> (m,C.opp c)) f 

  let mult f g =
    f |> L.map (fun t -> mult_term_poly t g)
      |> L.concat
      |> norm
  
  let minus f g = add f (opp g)

  let one  = [([], C.one)]
  
  let zero = []
  
  let var v = [([v],C.one)]
  
  let const c = [([],c)]

  let lmult = L.fold_left (fun acc f -> mult acc f) one

  let ladd  = L.fold_left (fun acc f -> add acc f) zero

  let vars f = sorted_nub (conc_map (fun (m,_) -> sorted_nub m) f)

  let partition p f =
    let (t1s, t2s) = L.partition p f in
    (norm t1s, norm t2s)

  let eval env f =
    let eval_monom m = lmult (L.map (fun v -> env v) m) in
    let eval_term (m,c) = mult (const c) (eval_monom m) in
    ladd (L.map eval_term f)

  let to_terms f = f

  let from_terms f = norm f

  let is_const = function [([],_c)] -> true | _ -> false

  let is_var = function [([_x],c)] when c = C.one -> true | _ -> false

  let ( *@) = mult
  let ( +@) = add
  let ( -@) = minus

end