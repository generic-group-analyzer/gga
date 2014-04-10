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

let mapi' f = List.mapi (fun i x -> f (i+1) x)