(* This file is distributed under the MIT License (see LICENSE). *)

(*s Synthesize SPS. *)

(*i*)
open Util
open LPoly
open LStringPoly
open InteractiveAnalyze

module IR = IntRing
(*i*)

type setting = TY1 | TY2 | TY3

let gnames_of_setting = function
  | TY1       -> ("G","G")
  | TY2 | TY3 -> ("G1","G2")

type sps_scheme = {
  key_left    : SP.t list;
  key_right   : SP.t list;
  sig_left    : SP.t list;
  sig_right   : SP.t list;
  (* we use these names for the given values in the game definition *)
  msg_left_n  : string list;
  msg_right_n : string list;
  sig_left_n  : string list;
  sig_right_n : string list;
  setting     : setting;
  osample     : string list
}

(*******************************************************************)
(* \hd{Computation of verification equations} *)

let get_vars ps = conc_map SP.vars ps |> sorted_nub S.compare

let completion sps =
  let left = match sps.setting with
    | TY1 | TY2 ->
      (sps.key_left   @ sps.key_right
       @ L.map SP.var (sps.msg_left_n @ sps.msg_right_n @ sps.sig_left_n @ sps.sig_right_n))
      |> sorted_nub SP.compare
    | TY3 ->
      (sps.key_left @ L.map SP.var (sps.msg_left_n @ sps.sig_left_n))
      |> sorted_nub SP.compare
  in
  let right = match sps.setting with
    | TY1 ->
      sorted_nub SP.compare
        (  sps.key_left @ sps.key_right
         @ L.map SP.var (sps.msg_left_n @ sps.msg_right_n @ sps.sig_left_n @ sps.sig_right_n))
    | TY2 | TY3 ->
      sorted_nub SP.compare (sps.key_right @ L.map SP.var (sps.msg_right_n @ sps.sig_right_n))
  in
  let total_left  = SP.one :: left in
  let total_right = SP.one :: right in
  conc_map (fun l -> L.map (fun r -> SP.(l *@ r)) total_right) total_left
  |> sorted_nub SP.compare

(* Takes the completion of the inputs and returns a list of all monomials appearing in it *)
let basis c =
  conc_map SP.mons c
  |> sorted_nub (fun x y -> SP.compare (SP.from_mon x) (SP.from_mon y))

let poly_to_vector = SP.to_vector

let vector_to_poly v b =
  let rec loop acc v b =
    match (v,b) with
    | (x :: vs, y :: bs) -> SP.(loop (acc +@ (const x) *@ (from_mon y)) vs bs)
    | ([], []) -> acc
    | _ -> failwith "Vector and basis do not match."
  in
  loop SP.zero v b

let poly_list_to_matrix ps b =
  L.map (fun p -> poly_to_vector p b) ps

let pp_matrix m =
  L.iter (fun l -> F.printf "| %a | \n" (pp_list ",  \t" SP.pp_coeff) l) m

let kernel_to_eqns vs c =
  let vec_to_eqn v =
    let rec loop acc i w =
      match w with
      | [] -> acc
      | x :: ws -> SP.(loop (acc +@ (const x *@ (L.nth c i))) (i+1) ws)
    in
    loop SP.zero 0 v
  in
  L.map vec_to_eqn vs

(*******************************************************************)
(* \hd{Instantiation} *)

(* Creates the map that substitutes for labels S etc. in the signature their
   expression in terms of keys, messages and random variables. *)
let make_eval_map sps =
  let vars = sps.sig_left_n @ sps.sig_right_n in
  let vals = sps.sig_left @ sps.sig_right in
  let z = L.combine vars vals in
  (fun x -> try L.assoc x z with _ -> SP.var x)

let instantiate_poly subst p =
  let evalf x =
    try SP.from_int (L.assoc x subst)
    with _ -> SP.var x
  in
  SP.eval evalf p

(* Instantiates an sps template by applying subst *)
let instantiate_template sps subst =
  { sps with
    sig_left  = L.map (instantiate_poly subst) sps.sig_left;
    sig_right = L.map (instantiate_poly subst) sps.sig_right
  }

(*******************************************************************)
(* \hd{Pretty printing of game definition} *)

let get_oparams sps =
  let (g1,g2) = gnames_of_setting sps.setting in
  let append_type t x = (x,t) in
    (L.map (append_type g1) sps.msg_left_n)
  @ (L.map (append_type g2) sps.msg_right_n)

let get_wc_params sps =
  let (g1,g2) = gnames_of_setting sps.setting in
  let append_type t x = ("w" ^ x,t) in
     L.map (append_type g1) (sps.msg_left_n  @  sps.sig_left_n)
  @ L.map (append_type g2) (sps.msg_right_n @ sps.sig_right_n)

(* Takes a polynomial and renames each variable by applying [ren]. *)
let rename_vars sps ren poly =
  let vars =
    sps.sig_left_n @ sps.sig_right_n @ sps.msg_left_n @ sps.msg_right_n @ sps.osample
    |> sorted_nub S.compare
  in
  let renaming = L.combine vars (L.map (fun v -> SP.var (ren v)) vars) in
  SP.eval (fun x -> try L.assoc x renaming with Not_found -> SP.var x) poly

let make_game ?(rma=false) ?(ubt=false) sps vereqs =
  let buf = Buffer.create 1024 in
  let fmt = Format.formatter_of_buffer buf in
  let (g1, g2) = gnames_of_setting sps.setting  in
  let random_sigs sigs msgs =
    if not rma then []
    else L.map (rename_vars sps (fun v -> "s"^v)) (sigs @ L.map SP.var msgs)
  in

  let weqs = L.map (fun p -> ("0 = ",p)) (L.map (rename_vars sps (fun v -> "w"^v)) vereqs) in
  let wineqs =
    L.map (fun p -> ("forall i: 0 <> ",p))
     (L.map (fun v -> SP.(var ("w"^v) -@ var (v^"_i"))) (sps.msg_right_n @ sps.msg_left_n))
  in

  let print_input xs g comment =
    if xs <> [] then
      F.fprintf fmt "input [ %a ] in %s. (* %s *)\n"
        (pp_list ", " SP.pp) xs g comment
  in

  let pp_sample fmt v =
    F.fprintf fmt "sample %s" v
  in

  let pp_ggt fmt f =
    match SP.mons f with
    | [] | [_] ->
      SP.pp fmt f
    | mon0 :: mons ->
      let m_ggt = List.fold_left (fun m_ggt m -> SP.ggt_mon m_ggt m) mon0 mons in
      let f = SP.div_mon f m_ggt in
      if SP.is_const (SP.from_mon m_ggt)
      then SP.pp fmt f
      else F.fprintf fmt "(%a)*%a" SP.pp f SP.pp_monom m_ggt
  in

  (* print setting *)
  if ubt then (
    let setting = match sps.setting with TY1 -> "1" | TY2 -> "2" | TY3 -> "3" in
    F.fprintf fmt "group_setting %s.\n" setting
  ) else (
    F.fprintf fmt "map %s * %s -> GT.\n" g1 g2;
    if sps.setting = TY2 then F.fprintf fmt "iso G2 -> G1.\n";
    F.fprintf fmt "\n";
  );

  let global_rvars = get_vars (sps.key_left @ sps.key_right) in

  F.fprintf fmt "sample %a.\n" (pp_list "," pp_string) global_rvars;

  (* print verification keys *)
  print_input sps.key_left g1 "keys left";
  print_input sps.key_right g2 "keys right";
  F.fprintf fmt "\n";

  (* print signatures for random message attack *)
  if rma then (
    let sig_rvars =
      get_vars (random_sigs sps.sig_left sps.msg_left_n @ random_sigs sps.sig_right sps.msg_right_n)
      |> sorted_nub compare
      |> L.filter (fun v -> not (L.mem v global_rvars))
    in
    F.fprintf fmt "sample %a.\n" (pp_list "," pp_string) sig_rvars;
    print_input (random_sigs sps.sig_left sps.msg_left_n)   g1 "random left";
    print_input (random_sigs sps.sig_right sps.msg_right_n) g2 "random right";
    F.fprintf fmt "\n";
  );

  (* print oracle *)
  F.fprintf fmt
    ("oracle o1(%a) =\n"^^
     "  %a" ^^
     "  return\n"^^
     "    [%a] in %s,\n"^^
     "    [%a] in %s.\n")
    (pp_list ", " (pp_tuple ":" pp_string))  (get_oparams sps)
    (pp_list' ";\n  " pp_sample) sps.osample
    (pp_list ", " pp_ggt) sps.sig_left g1
    (pp_list ", " pp_ggt) sps.sig_right g2;
  F.fprintf fmt "\n";

  let wineqs =
    if not rma then wineqs
    else wineqs @ (L.map (fun vm -> ("0 <> ", SP.(var ("s"^vm) -@ var ("w"^vm))))
                     (sps.msg_right_n @ sps.msg_left_n))
  in
  (* print winning condition *)
  F.fprintf fmt "win (%a) =\n  (   %a@\n   /\\ %a)."
    (pp_list "," (pp_tuple ":" pp_string)) (get_wc_params sps)
    (pp_list "@\n   /\\ " (pp_pair' pp_string SP.pp)) weqs
    (pp_list "@\n   /\\ " (pp_pair' pp_string SP.pp)) wineqs;
  F.fprintf fmt "\n";

  Buffer.contents buf

(*******************************************************************)
(* \hd{Synthesis with templates} *)

type coeff = string

type synth_spec = {
  sps_t           : sps_scheme;
  vars            : coeff list;
  choices         : int list;
  symmetries      : (SP.t list) * ((SP.t * SP.t) list) list;
  equivsigs       : (SP.t list) list;
  nonzero_constrs : SP.t list;
  zero_constrs    : SP.t list
}

let var_gen () =
  let vars = ref [] in
  let ctr  = ref 0 in
  let gen () =
    let  v = F.sprintf "c%i" !ctr in
    vars := !vars@[F.sprintf "c%i" !ctr]; incr ctr; SP.var v
  in
  (vars, gen)
