(*i*)
open Util
open Nondet
open LPoly
open LStringPoly
open InteractiveAnalyze
open Synthesis

module IR = IntRing
(*i*)

let synth_spec countonly spec specname =
  let i_total = ref 0 in
  let i_secure = ref 0 in
  let i_attack = ref 0 in
  let i_unknown = ref 0 in
  let i_verif = ref 0 in
  let mkdir s = try Unix.mkdir s 0o700 with _ -> () in
  let prefix = "gen/"^specname in
  mkdir prefix;
  mkdir (prefix^"/noverif");
  mkdir (prefix^"/attack");
  mkdir (prefix^"/sigrand");
  mkdir (prefix^"/error");

  let analyze_sig v =
    incr i_total;

    let sps = instantiate_template spec.sps_t (L.combine spec.vars v) in
    (* Compute the completion using the _t polynomials *)
    let tmpl = completion sps in
    (* Substitute for actual value of labels into the completion *)
    let c = L.map (SP.eval (make_eval_map sps)) tmpl in
    let b = basis c in
    let m = poly_list_to_matrix c b in
    let left_kernel = L.map (fun x -> L.map Big_int.big_int_of_int x) (Pari_Ker.kernel m) in
    
    if left_kernel = [] then (
      let sgdef = make_game sps [] in
      output_file (F.sprintf "./%s/noverif/sps_%02i.ec" prefix !i_total) sgdef;
      F.printf "%i noeq %!" !i_total
    ) else (
      incr i_verif;
      if countonly then (
        incr i_unknown;
        let eqs = kernel_to_eqns left_kernel tmpl in
        let sgdef = make_game sps eqs in
        output_file (F.sprintf "./%s/sps_%02i.ec" prefix !i_unknown) sgdef
      ) else (
        let eqs = kernel_to_eqns left_kernel tmpl in
        let sgdef = make_game sps eqs in
        let srgdef = make_game ~rma:true sps eqs in
        let res =
          try
            analyze_bounded_from_string ~counter:true ~fmt:null_formatter sgdef 1
          with
            InteractiveBounded.InvalidGame e -> Z3_Solver.Error e
        in
        match res with
        | Z3_Solver.Valid ->
          incr i_secure;
          output_file (F.sprintf "./%s/sps_%02i.ec" prefix !i_secure) sgdef;
          output_file (F.sprintf "./%s/sigrand/sps_%02i.ec" prefix !i_secure) srgdef
        | Z3_Solver.Unknown ->
          if !i_total mod 10 = 0 then F.printf "\n%i? %!\n" !i_total;
          incr i_unknown
        | Z3_Solver.Attack _ ->
          output_file (F.sprintf "./%s/attack/sps_%02i.ec" prefix !i_attack) sgdef;
          F.printf "\n%i! %!\n" !i_total;
          incr i_attack;
        | Z3_Solver.Error e ->
          output_file (F.sprintf "./%s/error/sps_%02i.ec" prefix !i_unknown) sgdef;
          F.printf "Error: %s\n" e;
          incr i_unknown
      )
    )
  in

  Pari_Ker.pari_init ();

  let vec_leq v1 v2 = 0 <= list_compare Pervasives.compare v1 v2 in
  let apply_symmetry sym cs =
    let perm = sym @ L.map (fun (x,y) -> (y,x)) spec.symmetry in
    L.mapi (fun i c -> try L.nth cs (find_idx spec.vars (L.assoc (L.nth spec.vars i) perm)) with Not_found -> c) cs
  in
  let nonzero cs var = L.nth cs (find_idx spec.vars var) <> 0 in
  let iszero cs var = L.nth cs (find_idx spec.vars var) = 0 in
  let coeffs =
    nprod (mconcat [0; 1]) (L.length spec.vars) >>= fun cs ->
    guard (
      L.for_all (L.exists (fun var -> nonzero cs var)) spec.nonzero_constrs &&
      L.for_all (L.exists (fun var -> iszero cs var)) spec.zero_constrs &&
      (* (vec_leq cs (L.map (fun v -> v*(-1)) cs)) &&   *)            (* symmetry: adversary can multiply vector with -1 *)
      (vec_leq cs (apply_symmetry spec.symmetry cs))                  (* symmetry, e.g., V and W might be equivalent *)
    ) >> ret cs
  in

  iter (-1) coeffs analyze_sig;

  let res =
    F.sprintf
      "\n\n%i Checked: %i no verification equation / %i secure / %i attack / %i unknown\n"
      !i_total (!i_total - !i_verif) !i_secure !i_attack  !i_unknown
  in
  output_file (F.sprintf "./%s/results" prefix) res;
  print_endline res


let synth countonly specname =
  let specs =
    [ ("II.1",SpecII.spec1)
    ; ("II.2",SpecII.spec2)
    ; ("II.3",SpecII.spec3)
    ; ("II.4",SpecII.spec4)
    ; ("III.1",SpecIII.spec1)
    ; ("III.2",SpecIII.spec2)
    ]
  in
  let spec = L.assoc specname specs in
  synth_spec countonly spec specname
