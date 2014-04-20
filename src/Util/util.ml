(*s This module provides some general purpose utility functions. *)

(*i*)
module F = Format
module L = List
(*i*)

(*******************************************************************)
(* \hd{List functions} *)

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
let sorted_nub xs =
  xs |> L.sort compare  |> group (=) |> L.map L.hd

(* \ic{%
   [mapi' f xs] returns the list where the [i]-th
   element is computed as [f i xs[i]] using $1$-indexing.} *)
let mapi' f = L.mapi (fun i x -> f (i+1) x)

(* \ic{Composition of [concat] and [map].} *)
let conc_map f xs = L.concat (L.map f xs)

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