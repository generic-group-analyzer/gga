open Lazy

(* Nondeterminism Monad *)

type 'a nnode =
    Nil
  | Cons of 'a * 'a nondet
and 'a nondet = 'a nnode Lazy.t

let mempty = lazy Nil

let ret a = lazy (Cons (a, mempty))

(* Combine results returned by [a] with results
   returned by [b]. Results from [a] and [b] are
   interleaved. *)
let mplus (a : 'a nondet) (b : 'a nondet) : 'a nondet =
  let rec go a b =
    match force a with
    | Nil           -> b
    | Cons (a1, a2) -> lazy (Cons (a1, go a2 b))
  in
  go a b


let bind (m : 'a nondet) (f : 'a -> 'b nondet) : 'b nondet =
  let rec go m =
    match force m with
    | Nil         -> lazy Nil
    | Cons (a, b) -> mplus (f a) (go b)
  in
  go m

(* Execute and get first [n] results as list,
   use [n = -1] to get all values. *)
let run n m =
  let rec go n m acc =
    if n = 0 then List.rev acc
    else
      match force m with
      | Nil         -> List.rev acc
      | Cons (a, b) -> go (pred n) b (a::acc)
  in go n m []

let guard pred =
  if pred then ret () else mempty

(* Apply function [f] to the first n values,
   use [n = -1] to apply [f] to all values. *)
let iter n m f =
  let rec go n m =
    if n = 0 then ()
    else
      match force m with
      | Nil         -> ()
      | Cons (a, b) -> f a; go (pred n) b
  in go n m


let sequence ms =
  let go m1 m2 =
    bind m1 (fun x ->
    bind m2 (fun xs ->
    ret (x::xs)))
  in
  List.fold_right go ms (ret [])


let mapM f ms = sequence (List.map f ms)
let foreachM ms f = mapM f ms

let rec msum ms =
  match ms with
  | m::ms -> mplus m (msum ms)
  | []    -> mempty

let rec mconcat ms =
  match ms with
  | m::ms -> mplus (ret m) (mconcat ms)
  | []    -> mempty

let (>>=) = bind

let (>>) m1 m2 = m1 >>= fun _ -> m2


(* \ic{Return all subsets $S$ of $m$ such that $|S| \leq k$.} *)
let pick_set k m =
  let rec go k acc =
    mplus
      (ret acc)
      (guard (k <> 0) >>
       m >>= fun x ->
       guard ((List.for_all (fun y -> y < x) acc)) >>
       go (k-1) (x::acc))
  in
  go k []

(* \ic{Return the cartesian product of $m1$ and $m2$.} *)
let cart m1 m2 =
  m1 >>= fun x1 ->
  m2 >>= fun x2 ->
  ret (x1,x2)

(* \ic{Return the cartesian product of $m$.} *)
let prod m = cart m m

(* \ic{Return the $n$-fold cartesian product of $ms$.} *)
let rec ncart ms =
  match ms with
  | []    -> ret []
  | m::ms ->
    m >>= fun x ->
    ncart ms >>= fun xs ->
    ret (x::xs)

(* \ic{Return the $n$-fold cartesian product of $m$.} *)
let nprod m n =
  let rec go n acc =
    if n <= 0 then ret acc
    else m >>= fun x -> go (n-1) (x::acc)
  in
  go n []
