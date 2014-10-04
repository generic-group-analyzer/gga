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
  let i_error = ref 0 in
  let i_unknown = ref 0 in
  let i_verif = ref 0 in
  let mkdir s = try Unix.mkdir s 0o700 with _ -> () in
  let prefix = "gen/"^specname in
  mkdir prefix;
  mkdir (prefix^"/noverif");
  mkdir (prefix^"/attack");
  mkdir (prefix^"/unknown");
  mkdir (prefix^"/sigrand");
  mkdir (prefix^"/error");
  mkdir (prefix^"/tmp");
  mkdir (prefix^"/count");

  let analyze gdef n tryproof tryattack () =
    try
      analyze_bounded_from_string ~counter:tryattack ~proof:tryproof ~fmt:null_formatter gdef n
    with
      InteractiveBounded.InvalidGame e -> Z3_Solver.Error e
  in

  let analyze_external gdef n time tryproof tryattack () =
    let fname = prefix^"/tmp/sps.ec" in
    output_file fname  gdef;
    let aorp = if tryattack && tryproof then "" else if tryproof then "p" else "a" in
    let res = Sys.command (F.sprintf "gtimeout %i ./ggt.native interactive%s_%i %s >/dev/null 2>&1" time aorp n fname) in
    if res = 0 then Z3_Solver.Valid
    else if res = 1 then Z3_Solver.Attack "attack not preserved"
    else Z3_Solver.Unknown "External call timed out or did not return valid"
  in
  
  let refine_analz checks =
    let rec go checks =
      match checks with
      | [] -> Z3_Solver.Unknown "no check returned result"
      | (name,check,proof_strongest)::checks ->
        F.printf "try %s\n%!" name;
        let res = check () in
        begin match res with
        | Z3_Solver.Attack _ | Z3_Solver.Error _ -> res
        | Z3_Solver.Valid when proof_strongest -> res
        | Z3_Solver.Valid -> Z3_Solver.Unknown ("Proof up to "^name)
        | _ -> go checks
        end
    in
    go checks
  in

  let analyze_sig v =
    incr i_total;

    let sps = instantiate_template spec.sps_t (L.combine spec.vars v) in
    (* Compute the completion using the _t polynomials *)
    let tmpl = completion sps in
    (* Substitute for actual value of labels into the completion *)
    let c = L.map (SP.eval (make_eval_map sps)) tmpl in
    let b = basis c in
    let m = poly_list_to_matrix c b in
    (*
    F.printf "completion: %a\n\n" (pp_list "," SP.pp) tmpl;
    F.printf "basis:\n %a\n\n" (pp_list ",\t" SP.pp) (L.map SP.from_mon b);
    pp_matrix m;
    F.printf "\n";
    *)
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
        output_file (F.sprintf "./%s/count/sps_%02i.ec" prefix !i_unknown) sgdef
      ) else (
        let eqs = kernel_to_eqns left_kernel tmpl in
        let sgdef = make_game sps eqs in
        let srgdef = make_game ~rma:true sps eqs in
        let checks1 =
          [ (* try to find fast attacks *)
            ("0-CMA attack", analyze sgdef 0 false true)
          ; ("1-RMA attack", analyze srgdef 0 false true)
          ; ("1-CMA attack", analyze_external sgdef 1 30 false true)
          (* try to find proofs, if we find a proof, we are done *)
          ; ("2-CMA proof", analyze_external sgdef 2 30 true false) ]
        in
        let check2 = 
          [ ("(1-CM+1-RM)A proof", analyze_external srgdef 1 30 true false)
          ; ("1-CMA", analyze_external sgdef 1 30 true false)
          (* try to find attacks *)
          ; ("(1-CM+1-RM)A attack", analyze_external srgdef 1 30 false true)
          ; ("2-CMA attack", analyze_external sgdef 2 30 false true)
          ]
        in
        let res =
          refine_analz
            (L.map (fun (x,y) -> (x,y,true)) checks1 @ L.map  (fun (x,y) -> (x,y,false)) check2)
        in
        match res with
        | Z3_Solver.Valid ->
          incr i_secure;
          F.printf "%i %!\n" !i_total;
          output_file (F.sprintf "./%s/sps_%02i.ec" prefix !i_secure) sgdef;
          output_file (F.sprintf "./%s/sigrand/sps_%02i.ec" prefix !i_secure) srgdef
        | Z3_Solver.Unknown s ->
          output_file (F.sprintf "./%s/unknown/sps_%02i.ec" prefix !i_unknown) ("(* "^s^" *)\n"^sgdef);
          F.printf "%i? %!\n" !i_total;
          F.printf "Unknown: %s\n" s;
          incr i_unknown
        | Z3_Solver.Attack _ ->
          output_file (F.sprintf "./%s/attack/sps_%02i.ec" prefix !i_attack) sgdef;
          F.printf "%i! %!\n" !i_total;
          incr i_attack;
        | Z3_Solver.Error e ->
          output_file (F.sprintf "./%s/error/sps_%02i.ec" prefix !i_error) sgdef;
          F.printf "Error: %s\n" e;
          incr i_error
      )
    )
  in

  Pari_Ker.pari_init ();

  let vec_leq v1 v2 = 0 <= list_compare Pervasives.compare v1 v2 in
  let apply_symmetry sym cs =
    let get_var p =
      match SP.vars p with
      | [s] -> s 
      | _ -> failwith "symmetry must be list of variable polynomials"
    in
    let sym = L.map (fun (p1,p2) -> (get_var p1,get_var p2)) sym in
    let perm = sym @ L.map (fun (x,y) -> (y,x)) sym in
    L.mapi (fun i c -> try L.nth cs (find_idx spec.vars (L.assoc (L.nth spec.vars i) perm)) with Not_found -> c) cs
  in
  let lookup_var cs v = L.nth cs (find_idx spec.vars v) in
  let eval_poly p cs =
    SP.eval (fun v -> SP.from_int (lookup_var cs v)) p
  in
  let coeffs =
    nprod (mconcat spec.choices) (L.length spec.vars) >>= fun cs ->
    guard (
      L.for_all (fun constr -> not (SP.equal SP.zero (eval_poly constr cs))) spec.nonzero_constrs &&
      L.for_all (fun constr -> (SP.equal SP.zero (eval_poly constr cs))) spec.zero_constrs &&
      (* (vec_leq cs (L.map (fun v -> v*(-1)) cs)) &&   *)                     (* symmetry: adversary can multiply vector with -1 *)
      L.for_all (fun sym -> vec_leq cs (apply_symmetry sym cs)) spec.symmetries (* symmetry, e.g., V and W might be equivalent *)
    ) >> ret cs
  in

  let t_before = Unix.time () in
  iter (-1) coeffs analyze_sig;
  let t_after = Unix.time () in
  let res =
    F.sprintf
      "\n\n%i Checked in %.2fs: %i no verification equation / %i secure / %i attack / %i unknown / %i error\n"
      !i_total (t_after -. t_before) (!i_total - !i_verif) !i_secure !i_attack !i_unknown !i_error
  in
  output_file (F.sprintf "./%s/results" prefix) res;
  print_endline res

let synth countonly specname =
  let specs =
    [ ("II.1",SpecII.spec1)
    ; ("II.2",SpecII.spec2)
    ; ("II.3",SpecII.spec3)
    ; ("II.4",SpecII.spec4)
    ; ("II_mixed.1",SpecII_mixed.spec1)
    ; ("II_mixed.2",SpecII_mixed.spec2)
    ; ("II_mixed.3",SpecII_mixed.spec3)
    ; ("III.1",SpecIII.spec1)
    ; ("III.2",SpecIII.spec2)
    ; ("III.3",SpecIII.spec3)
    ; ("III.4",SpecIII.spec4)
    ]
  in
  let spec = L.assoc specname specs in
  synth_spec countonly (spec ()) specname
