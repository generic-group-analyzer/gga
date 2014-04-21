(*s This module provides some general purpose utility functions. *)

(*i*)
module F = Format
module L = List
(*i*)

(*******************************************************************)
(* \hd{List functions, option functions, \ldots } *)

(* \ic{%
   [group rel xs] creates a list of lists where successive
   elements of [xs] that are related with respect to [rel]
   are grouped together. This function is commonly used
   together with [L.sort] to compute the equivalence
   classes of elements in [xs] with respect to [rel].} *)
let group rel xs =
  let rec go xs y acc = match xs with
    | []                 -> [ L.rev acc ]
    | x::xs when rel x y -> go xs y (x::acc)
    | x::xs              -> (L.rev acc)::go xs x [x] 
  in
  match xs with
  | []    -> []
  | x::xs -> go xs x [x]

(* \ic{%
    [sorted_nub xs] sorts the elements in [xs] and
    removes duplicate occurences in [xs].} *)
let sorted_nub cmp xs =
  xs |> L.sort cmp |> group (fun a b -> cmp a b = 0) |> L.map L.hd

(* \ic{%
   [mapi' f xs] returns the list where the [i]-th
   element is computed as [f i xs[i]] using $1$-indexing.} *)
let mapi' f = L.mapi (fun i x -> f (i+1) x)

(* \ic{Composition of [concat] and [map].} *)
let conc_map f xs = L.concat (L.map f xs)

(* \ic{[from_opt f def ox] takes an option value [ox] and
       applies [f] if possible, otherwise def is returned.} *)
let from_opt f def ox =
  match ox with
  | None   -> def
  | Some x -> f x

(* \ic{[id] is the identity function} *)
let id x = x

(* \ic{[list_equal e_equal l1 l2] returns true if the two lists are
       equal with respect to [e_equal].} *)
let list_equal eq xs0 ys0 =
  let rec go xs ys = 
    match xs,ys with
    | [], []       -> true
    | x::xs, y::ys -> eq x y && go xs ys
    | _            -> assert false
  in
  (L.length xs0 = L.length ys0) && go xs0 ys0

(* \ic{[list_compare e_compare l1 l2] compares the two lists
        with respect to length and [e_compare].} *)
let list_compare cmp xs0 ys0 =
  let rec go xs ys =
    match xs, ys with
    | [], []       -> 0
    | x::xs, y::ys ->
      let d = cmp x y in
      if d <> 0 then d
      else go xs ys
    | _            -> assert false
  in
  let d = L.length xs0 - L.length ys0 in
  if d > 0 then 1
  else if d < 0 then -1
  else go xs0 ys0

(* \ic{Returns the cartesian product of a list of lists.} *)
let cart_prod xss0 =
  let rec go acc xss =
    match xss with
    | []      -> acc
    | xs::xss ->
      let acc = conc_map (fun x -> L.map (fun ys -> x::ys) acc) xs in
      go acc xss
  in go [[]] (L.rev xss0)

(* \ic{Set of strings.} *)
module Ss = Set.Make(struct type t = string let compare = compare end)

(* \ic{Convert list of strings to set of strings.} *)
let ss_of_list = L.fold_left (fun acc x -> Ss.add x acc) Ss.empty

(* \ic{Map where keys are strings.} *)
module Ms = Map.Make(struct type t = string let compare = compare end)

(* \ic{[add_set k v m] adds the value [val] to [m] for the key [key].} *)
let add_set empty add k v m =
  let old_vs =
    try  Ms.find k m
    with Not_found -> empty
  in
  Ms.add k (add v old_vs) m

let ss_add_set = add_set Ss.empty Ss.add

(*******************************************************************)
(* \newpage\hd{File IO} *)

(* \ic{%
   [input_file filename] returns the content of [filename] as a string.} *)
let input_file filename =
  let in_channel = open_in filename in
  let rec go lines =
    try
      let l = input_line in_channel in
      go (l :: lines)
    with
      End_of_file -> lines
  in
  let lines = go [] in
  let _ = close_in_noerr in_channel in
  String.concat "\n" (L.rev lines)

(* \ic{%
    [output_file filename content] writes the string [content]
    to [filename].} *)
let output_file filename content =
  let out_channel = open_out filename in
  output_string out_channel content;
  close_out_noerr out_channel

(*i*)
(*******************************************************************)
(* \hd{Pretty printing} *)

let rec pp_list sep pp_elt f l =
  match l with
  | [] -> ()
  | [e] -> pp_elt f e 
  | e::l -> Format.fprintf f "%a%(%)%a" pp_elt e sep (pp_list sep pp_elt) l 

let pp_list_c pe = (pp_list "," pe)
let pp_list_s = pp_list_c (fun fmt -> Format.fprintf fmt "%s")

let pp_int fmt i = Format.fprintf fmt "%i" i

let pp_string fmt s = Format.fprintf fmt "%s" s

let pp_option pp_some fmt o = match o with
  | Some(x) -> pp_some fmt x
  | None    -> Format.fprintf fmt " - "
(*i*)