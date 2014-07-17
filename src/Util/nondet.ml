open Lazy

(* Nondeterminism Monad *)

type 'a stream =
    Nil
  | Cons of 'a * ('a stream) lazy_t

type 'a nondet = 'a stream lazy_t

let mempty = lazy Nil

let ret a = lazy (Cons (a, mempty))

let guard pred =
  if pred then ret () else mempty

(* Combine results returned by a with results
   returned by b. Results from a and b are
   interleaved. *)
let rec mplus a b = from_fun (fun () ->
  match force a with
  | Cons (a1, a2) -> Cons (a1, mplus b a2)
  | Nil           ->
    begin match force b with
    | Nil           -> Nil
    | Cons (b1, b2) -> Cons (b1, mplus a b2)
    end)

let rec bind m f = from_fun (fun () ->
  match force m with
  | Nil         -> Nil
  | Cons (a, b) -> force (mplus (f a) (bind b f)))

(* Execute and get first n results as list,
   use n = -1 to get all values. *)
let run n m =
  let rec go n m acc =
    if n = 0 then List.rev acc
    else
      match force m with
      | Nil         -> List.rev acc
      | Cons (a, b) -> go (pred n) b (a::acc)
  in go n m []

(* Apply function f to the first n values,
   use n = -1 to apply f to all values. *)
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
