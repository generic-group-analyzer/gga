(*s Analyze non-parametric problem *)
(*i*)
open Util
open Poly
open NonParamInput
open NonParamCompletion
(*i*)

(*i*)
let cdh_asym1 =
  let inputs =
    [ 
      { ge_rpoly = RP.var "X"; ge_group = "1" }
    ; { ge_rpoly = RP.var "Y"; ge_group = "2" }
    ; { ge_rpoly = RP.var "U"; ge_group = "1:2" }
    ]
  in
  let chal = { ge_rpoly = RP.add
                            (RP.var "U")
                            (RP.mult (RP.var "X") (RP.var "Y"));
               ge_group = "1:2" }
  in
  mk_computational
    NonParamPredefined.gs_bilinear_asym
    inputs
    chal

let cdh_asym2 =
  let inputs =
    [ { ge_rpoly = RP.var "X"; ge_group = "2" }
    ; { ge_rpoly = RP.var "Y"; ge_group = "2" }
    ; { ge_rpoly = RP.var "U"; ge_group = "1:2" }
    ]
  in
  let chal = { ge_rpoly = RP.add
                            (RP.var "U")
                            (RP.mult (RP.var "X") (RP.var "Y"));
               ge_group = "1:2" }
  in
  mk_computational
    NonParamPredefined.gs_bilinear_asym
    inputs
    chal

let cdh_asym3 =
  let inputs =
    [ { ge_rpoly = RP.var "X"; ge_group = "2" }
    ; { ge_rpoly = RP.var "Y"; ge_group = "2" }
    ; { ge_rpoly = RP.var "U"; ge_group = "1:2" }
    ]
  in
  let chal = { ge_rpoly = RP.add
                            (RP.var "U")
                            (RP.mult (RP.var "X") (RP.var "Y"));
               ge_group = "1:2" }
  in
  mk_computational
    NonParamPredefined.gs_bilinear_asym
    inputs
    chal

let dassm =
  let linputs =
    [ { ge_rpoly = RP.var "X"; ge_group = "2" }
    ; { ge_rpoly = RP.var "Y"; ge_group = "2" }
    ; { ge_rpoly = RP.mult (RP.var "X") (RP.var "Y"); ge_group = "1:2" }
    ]
  in
  let rinputs =
    [ { ge_rpoly = RP.var "X"; ge_group = "2" }
    ; { ge_rpoly = RP.var "Y"; ge_group = "2" }
    ; { ge_rpoly = RP.var "U"; ge_group = "1:2" }
    ]
  in
  mk_decisional
    NonParamPredefined.gs_bilinear_asym
    linputs
    rinputs
(*i*)

type trace = string
type attack_info = string

type res =
  | Attack of trace * attack_info
  | Valid  of trace * int

let pp_result fmt res =
  let sep = "**********************************************************************" in
  match res with
  | Valid(info,i) ->
    F.fprintf fmt "%s" sep;
    F.fprintf fmt "%s\n" info;
    F.fprintf fmt  "%s\n" sep;
    F.fprintf fmt "The assumption is valid for all primes%s.\n"
      (if i = 1 then "" else " > "^string_of_int i)
  | Attack(info,ainfo) ->
    F.fprintf fmt "%s" sep;
    F.fprintf fmt "%s\n" info;
    F.fprintf fmt  "%s\n" sep;
    F.fprintf fmt "There is an attack: %s\n" ainfo

let get_vcomp comp =
  let mbasis = sorted_nub compare (conc_map RP.mons comp) in
  let vcomp = L.map (rp_to_vector mbasis) comp in
  (mbasis,vcomp)

let compl_info name inputs comp recipes mbasis vcomp cgid =
  let fmt = Format.str_formatter in
  F.fprintf fmt "\ninput %s:\n  %a\n" name (pp_list "\n  " pp_group_elem) inputs;
  F.fprintf fmt "\ncompletion %s (for group %a):\n" name pp_group_id cgid;
  F.fprintf fmt "%a \t(monomial basis)\n" (pp_list " \t" RP.pp_monom) mbasis;
  List.iter
    (fun (v,(f,r)) ->
        F.fprintf fmt "%a \t(%a using %a)\n" (pp_list "  \t" IntRing.pp) v
          RP.pp f pp_recipe r)
    (L.combine vcomp (L.combine comp recipes));
  Format.flush_str_formatter ()

let string_of_attack v recipes =
  let arecipe =
    L.concat (L.mapi
               (fun i a ->
                  let sa = if a = 1 then "" else string_of_int a^"*" in
                  if a = 0 then []
                  else [ fsprintf "%s%a" sa pp_recipe (L.nth recipes i) |> fsget ])
               v)
  in String.concat " + " arecipe

let check_computational gs inputs chal =

  (* \ic{%
     Compute completion of inputs in challenge group, monomial basis of
     completion, and vector representation of completion in monomial basis.} *)
  let (comps,recipes) = completion_for_group gs chal.ge_group [ inputs ] in
  let comp = L.hd comps in
  let (mbasis,vcomp) = get_vcomp comp in
  let info = compl_info "" inputs comp recipes mbasis vcomp chal.ge_group in

  (* \ic{Check if completion is missing any monomials occuring in challenge.} *)
  match L.filter (fun m -> not (List.mem m mbasis)) (RP.mons chal.ge_rpoly) with
  | m::_ ->
    let info =
      fsprintf
        ("%s\nThe monomial %a is included in the challenge, but not in the completion")
        info
        RP.pp_monom m
      |> fsget
    in

    (* \ic{FIXME: Bad prime is coefficient of monomial.} *)
    Valid(info,1)
  | [] ->
    let vchal = rp_to_vector mbasis chal.ge_rpoly in
    let info = 
      fsprintf "%s\nchallenge vector:\n%a \t(monomial basis)\n%a \t(%a)\n"
        info
        (pp_list "\t" RP.pp_monom) mbasis
        (pp_list " \t" IntRing.pp) vchal
        pp_group_elem chal
      |> fsget
    in
    begin match Sage_Solver.lin_solve vcomp vchal with
    | None   ->

      (* \ic{FIXME: think about bad primes here.} *)
      Valid(info,1)
    | Some sol ->
      let ainfo = "the challenge can be computed using "^(string_of_attack sol recipes) in
      Attack(info,ainfo)
    end

type side = Left | Right

let other_side = function Left -> Right | Right -> Left

let pp_side fmt s =
  F.fprintf fmt "%s" (match s with Left -> "left" | Right -> "right")

let check_decisional gs linputs rinputs =

  (* \ic{%
     Compute completion of inputs, monomial basis of completion, and vector
     representation of completion in monomial basis for right and left.} *)
  let (comps,recipes) = completion_for_group gs gs.cgs_target [ linputs; rinputs] in
  let lcomp, rcomp = match comps with [lc; rc] -> lc, rc | _ -> assert false in
  let (lmbasis,lvcomp) = get_vcomp lcomp in
  let (rmbasis,rvcomp) = get_vcomp rcomp in

  let linfo = compl_info "left" linputs lcomp recipes lmbasis lvcomp gs.cgs_target in
  let rinfo = compl_info "right" rinputs rcomp recipes rmbasis rvcomp gs.cgs_target in

  (* \ic{FIXME: Add left and right kernels to info.} *)
  let _lk,_rk,lonly,ronly,bp = Sage_Solver.compare_kernel lvcomp rvcomp in

  let attacks = (L.map (fun v -> (Left,v)) lonly)@(L.map (fun v -> (Left,v)) ronly) in
  match attacks with
  | [] ->
    Valid(linfo^rinfo, match maximum bp with None -> 1 | Some i -> i)
  | (s,v)::_ ->
    let ainfo =
      fsprintf
        ("the equality check for %s = 0 returns true in the %a game, "^^
         "but false in the %a game.")
        (string_of_attack v recipes)
        pp_side s
        pp_side (other_side s)
      |> fsget
    in
    Attack(linfo^rinfo,ainfo)

(* \ic{Check assumption.} *)
let check assm =
  match assm with
  | Computational(gs,inputs,chal) ->
    check_computational gs inputs chal
  | Decisional(gs,linputs,rinputs) ->
    check_decisional gs linputs rinputs

let test () =
  F.printf "Result 1:\n%a" pp_result (check cdh_asym1);
  F.printf "\nResult 2:\n%a" pp_result (check cdh_asym2);
  F.printf "\nResult 3:\n%a" pp_result (check dassm);
  exit 0
