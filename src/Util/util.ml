let rec pp_list sep pp_elt f l =
  match l with
  | [] -> ()
  | [e] -> pp_elt f e 
  | e::l -> Format.fprintf f "%a%(%)%a" pp_elt e sep (pp_list sep pp_elt) l 

let pp_list_c pe = (pp_list "," pe)
let pp_list_s = pp_list_c (fun fmt -> Format.fprintf fmt "%s")

let group pred xs =
  let rec go xs y acc = match xs with
    | []                  -> [ List.rev acc ]
    | x::xs when pred x y -> go xs y (x::acc)
    | x::xs               -> (List.rev acc)::go xs x [x] 
  in
  match xs with
  | []    -> []
  | x::xs -> go xs x [x]

let sorted_nub xs =
  xs |> List.sort compare  |> group (=) |> List.map List.hd

let pp_int fmt i = Format.fprintf fmt "%i" i

let pp_string fmt s = Format.fprintf fmt "%s" s

let pp_option pp_some fmt o = match o with
  | Some(x) -> pp_some fmt x
  | None    -> Format.fprintf fmt " - "

let mapi' f = List.mapi (fun i x -> f (i+1) x)

let input_file file_name =
  let in_channel = open_in file_name in
  let rec go lines =
    try
      let l = input_line in_channel in
      go (l :: lines)
    with
      End_of_file -> lines
  in
  let lines = go [] in
  let _ = close_in_noerr in_channel in
  String.concat "\n" (List.rev lines)

let output_file file_name content =
  let out_channel = open_out file_name in
  output_string out_channel content;
  close_out_noerr out_channel