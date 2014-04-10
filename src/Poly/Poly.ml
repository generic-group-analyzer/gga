(* Polynomials *)
open Util

module F = Format

module type Var = sig
  type t
  val pp : F.formatter -> t -> unit
end

module type Ring = sig
  type t
  val pp : F.formatter -> t -> unit
  val add : t -> t -> t
  val opp : t -> t
  val mult : t -> t -> t
  val one : t
  val zero : t
end

module MakePoly (V : Var) (C : Ring) = struct

  type coeff = C.t
  type var   = V.t

  (* invariant: sorted *)
  type monom = V.t list

  type term = C.t * monom

  type t = term list

  (* pretty printing *)
  let pp_monom fmt m =
    F.fprintf fmt "%a" (pp_list "*" V.pp) m

  let pp_term fmt (c,m) =
    if m = [] then F.fprintf fmt "%a" C.pp c
    else if c = C.one then pp_monom fmt m
    else F.fprintf fmt "%a*%a" C.pp c pp_monom m

  let pp fmt f =
    match f with
    | [] -> F.fprintf fmt "0"
    | _  -> F.fprintf fmt "%a" (pp_list "+" pp_term) f

  (* internal functions *)
  let norm f =
    f |> List.sort (fun (_c1,m1) (_c2,m2) -> compare m1 m2)
      |> group (fun (_,m1) (_,m2) -> m1 = m2)
      |> List.map
           (fun ys ->
              let (_,m) = List.hd ys in
              let c = List.fold_left (fun acc (c,_) -> C.add acc c) C.zero ys in
              (c,m))
      |> List.filter (fun (c,_) -> not (c = C.zero))
      |> List.sort compare (* FIXME: filter out (0,_) *)

  let mult_term (c,m) f =
    List.map (fun (c',m') -> (C.mult c c', List.sort compare (m @ m'))) f

  (* ring operations on polynomials *)
  let add f g = norm (f @ g)

  let opp f = List.map (fun (c,m) -> (C.opp c,m)) f 

  let mult f g =
    f |> List.map (fun t -> mult_term t g)
      |> List.concat
      |> norm
  
  let minus f g = add f (opp g)

  let one  = [(C.one, [])]
  
  let zero = []
  
  let var v = [(C.one,[v])]
  
  let const c = [(c,[])]

  let lmult = List.fold_left (fun acc f -> mult acc f) one

  let ladd  = List.fold_left (fun acc f -> add acc f) zero

  let vars f = sorted_nub (List.concat (List.map snd f))

  (* move somewhere else: terms : t -> (coeff, [var]) *)
  let partition p f =
    let (t1s, t2s) = List.partition p f in
    (norm t1s, norm t2s)

(*   let vdeg v f =
    let vdeg_mon vm =
      match List.filter (fun xs -> v = List.hd xs) (group (=) vm) with
      | []   -> 0
      | [vs] -> List.length vs
      | _    -> assert false

    in
    List.fold_left
      (List.map (fun (_,m) -> vdeg_mon ))
 *)
  let eval env f =
    let eval_monom m =
      lmult (List.map (fun v -> env v) m)
    in
    let eval_term (c,m) =
      mult (const c) (eval_monom m)
    in
    ladd (List.map eval_term f)
  let to_terms f = f

  let from_terms f = norm f
end

module IntRing = struct
  type t = int
  let pp fmt i = F.fprintf fmt "%i" i

  let add = (+)
  let opp a = - a
  let mult a b = a * b
  let one = 1
  let zero = 0
end