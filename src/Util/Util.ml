(*s This module provides some general purpose utility functions. *)

(*i*)
module F = Format
module L = List
module YS = Yojson.Safe
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

let indices xs =
  let c = ref (-1) in L.map (fun _ -> c := !c + 1; !c) xs

let zip_indices xs =
  let c = ref (-1) in L.map (fun x -> c := !c + 1; (!c,x)) xs

(* \ic{%
   [mapi' f xs] returns the list where the [i]-th
   element is computed as [f i xs[i]] using $1$-indexing.} *)
let mapi' f = L.mapi (fun i x -> f (i+1) x)

(* \ic{Composition of [concat] and [map].} *)
let conc_map f xs = L.concat (L.map f xs)

let catSome xs0 =
  let rec go xs acc =
    match xs with
    | [] -> L.rev acc
    | Some x::xs -> go xs (x::acc)
    | None::xs   -> go xs acc
  in
  go xs0 []

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

(* \ic{Return the the list consisting of [i] elements [a].} *)
let replicate a i =
  let rec go i acc =
    if i <= 0 then acc
    else go (i - 1) (a::acc)
  in
  go i []

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

(* \ic{Set of int pairs.} *)
module Sii = Set.Make(struct type t = int * int let compare = compare end)

(* \ic{Convert list of in pairs to set of strings.} *)
let sii_of_list = L.fold_left (fun acc x -> Sii.add x acc) Sii.empty

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

let maximum xs0 =
  let rec go m xs =
    match xs with
    | []    -> Some m
    | x::xs -> go (max x m) xs
  in
  match xs0 with
  | []    -> None
  | x::xs -> go x xs

type ('a,'b) either = Left of 'a | Right of 'b

let common_prefix eq xs ys =
  let rec go acc xs ys =
    match xs,ys with
    | x::xs, y::ys when eq x y ->
      go (x::acc) xs ys
    | _ -> (L.rev acc,xs,ys)
  in
  go [] xs ys

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

(* \ic{%
   [call_external script cmd linenum] calls script, outputs [cmd] to the standard input of
   script, and reads (up to) [linenum] lines which are returned.} *)
let call_external script cmd linenum =
  let (c_in, c_out) = Unix.open_process script in
  output_string c_out cmd;
  flush c_out;
  let rec loop o linenum =
    if linenum = 0 then o
    else (
      try
        let l = input_line c_in in
        loop (o @ [l]) (linenum - 1)
      with End_of_file ->
        ignore (Unix.close_process (c_in,c_out));
        o)
  in loop [] linenum

(*******************************************************************)
(* \hd{JSON parsing} *)

exception JsonError of string

let fail_json js s = raise (JsonError (s^YS.to_string js))

let get_assoc k js =
  match js with
  | `Assoc l ->
    begin try
      L.assoc k l
    with
      Not_found -> fail_json js ("get_assoc: key "^k^" not found in ")
    end
  | _  -> fail_json js "get_assoc: assoc expected, got "

let get_string js =
  match js with
  | `String s -> s
  | _         -> fail_json js "get_string: string expected, got "

let get_bool js =
  match js with
  | `Bool b -> b
  | _       -> fail_json js "get_bool: bool expected, got "

let get_vec js =
  match js with
  | `List is ->
    L.map (function `Int i -> i | js -> fail_json js "get_vec: expected int, got ") is
  | _        -> fail_json js "get_vec: expected list, got "

let get_int js =
  match js with
  | `Int b -> b
  | _       -> fail_json js "get_int: int expected, got "

let get_pair f1 f2 js =
  match js with
  | `List [ js1; js2 ] -> (f1 js1, f2 js2)
  | _                  -> fail_json js "get_pair: two element list expected, got "

let get_list f js =
  match js with
  | `List xs -> L.map f xs
  | _        -> fail_json js "get_list: expected list, got "

let get_matrix = get_list (get_list get_int)

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

let pp_tuple sep p fmt (a,b) =
  F.fprintf fmt "%a %s %a" p a sep p b

let fsprintf fm = Format.fprintf Format.str_formatter fm

let fsget _ = Format.flush_str_formatter ()
(*i*)