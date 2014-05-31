(*s Analysis for interactive assumptions. *)

(*i*)
open Util
open Poly

module FS = InteractiveFormalSum
module IR = IntRing
module II = InteractiveInput
module S = String

module YS = Yojson.Safe
(*i*)

(*i*)

(*********************************************************************)
(* \hd{Analyze game definitions} *)

(* \ic{Compute formal sum for group choice [gchoice] and [gdef].} *)
let fs_of_gdef gdef gchoice =
  FS.(

    (* \ic{Linear combinations of adversary input.} *)
    let conv_term_inp n (m,c) = (c, [ICoeff(gchoice,n)], L.map (fun v -> SRVar v) m) in
    let f1 =
      conc_map
        (fun (n,f) -> L.map (conv_term_inp n) (II.RP.to_terms f))
        (zip_indices gdef.II.gdef_inputs)
    in

    (* \ic{Linear combination for $n$-th output of oracle $o$.} *)
    let conv_term_orcl o n (m,c) =
      (c, OCoeff(gchoice,o,n,0)::(conc_map (function II.Param(id) -> [OParam((id,o),0)] | _ -> []) m)
      , conc_map (function II.SRVar(v) -> [SRVar(v)] | II.ORVar(v) -> [ORVar((v,o),0)] | _ -> []) m)
    in
    let lincomb o n f = L.map (conv_term_orcl o n) (II.OP.to_terms f) in
    let comb_orcl (o,fs) = conc_map (fun (n,f) -> lincomb o n f) (zip_indices fs) in
    let fos = conc_map comb_orcl gdef.II.gdef_odefs in
    of_terms (f1@fos)
  )

(* \ic{Compute formal sum for [wpoly] that can contain [GroupChoice]
    values, but not [OParam] values.} *)
let wpoly_to_fs gchoices oparams wp : FS.t =
  let eval_var v =
    match v with
    | II.GroupChoice(v) -> L.assoc v gchoices
    | II.FieldChoice(v) -> FS.(param (FieldChoice(v)))
    | II.RVar(v)        -> FS.(var (SRVar(v)))
    | II.OParam(v)      -> FS.(param (OParam((v,L.assoc v oparams),0)))
  in
  let eval_monom ms acc =
    L.fold_left (fun fs v -> FS.mult fs (eval_var v)) acc ms
  in
  L.fold_left
    (fun fs (m,c) -> FS.plus fs (eval_monom m (FS.const c)))
    FS.zero
    (II.WP.to_terms wp)

let simp_constr cstr =
  let is_minus_one c = IR.equal c (IR.opp IR.one) in
  let go (binders,fsp) =
    match fsp with
    | _ when L.for_all (fun (c,_) -> is_minus_one c) fsp ->
      (binders,L.map (fun (_,ps) -> (IR.one,ps)) fsp)
    | _ ->
      (binders,fsp)
  in
  go cstr

let zero_params eq_constrs =
  conc_map
    (function (_,[(c,[p])]) when not (IR.equal c IR.zero) -> [p] | _ -> [])
    eq_constrs

let equal_params eq_constrs =
  let go (_,fsp) =
    let pos, neg = L.partition (fun (c,_) -> IR.compare c IR.zero > 0) fsp in
    begin match pos, neg with
    | [(c1,[p1])], [(c2,[p2])] when IR.equal c1 IR.one && IR.equal (IR.opp c2) IR.one ->
      if compare p1 p2 > 0 then [(p1,p2)] else if compare p1 p2 < 0 then [(p2,p1)] else []
    | _ ->
      []
    end
  in
  conc_map go eq_constrs

let inequal_params qineq_constrs =
  let go c =
    match c with
    | [(_,fsp)] ->
      let pos, neg = L.partition (fun (c,_) -> IR.compare c IR.zero > 0) fsp in
      begin match pos, neg with
      | [(c1,[p1])], [(c2,[p2])] when IR.equal c1 IR.one && IR.equal (IR.opp c2) IR.one ->
        if compare p1 p2 > 0 then [(p1,p2)] else if compare p1 p2 < 0 then [(p2,p1)] else []
      | _ ->
        []
      end
    | _ ->
      []
  in
  conc_map go qineq_constrs

let nonzero_params ineq_constrs qineq_constrs =
  (conc_map
     (function [(_,[(c,[p])])] when not (IR.equal c IR.zero) -> [p] | _ -> [])
     qineq_constrs)
  @
  (conc_map
     (function [([],[(c,[p])])] when not (IR.equal c IR.zero) -> [p] | _ -> [])
     ineq_constrs)

let rec simp_constrs eq_constrs0 ineq_constrs0 qineq_constrs0 =

  let simp_zero zparams (binders,fsp) =
    let fsp' = L.filter (fun (_c,ps) -> not (L.exists (fun p -> L.mem p zparams) ps)) fsp in
    if L.length fsp' > 0 then (binders,fsp') else (binders,fsp)
  in
  
  let simp_nzero nzparams (binders,fsp) =
    match fsp with
    | [(c,ps)] ->
      let ps' = L.filter (fun p -> not (L.mem p nzparams)) ps in
      if L.length ps' > 0 then (binders,[(c,ps')]) else (binders,[(c,ps)])
    | _        ->
      (binders,fsp)
  in

  let simp_equal eq_params (binders,fsp) =
    (binders, L.map (fun (c,ps) ->
                       (c,L.map (fun p -> try (L.assoc p eq_params) with Not_found -> p) ps))
                    fsp)
  in

  (* \ic{$a*c = a * d \land c \neq d \Rightarrow a = 0$ } *)
  let simp_factor ineq_params (binders,fsp) =
    let pos, neg = L.partition (fun (c,_) -> IR.compare c IR.zero > 0) fsp in
    match pos, neg with
    | [(c1,[a1;b1])], [(c2,[a2;b2])] when IR.equal c1 IR.one && IR.equal (IR.opp c2) IR.one ->
      if    (b1 = b2 && (L.mem (a1,a2) ineq_params || L.mem (a2,a1) ineq_params))
         || (b1 = a2 && (L.mem (a1,b2) ineq_params || L.mem (b2,a1) ineq_params))
      then (binders, [(IR.one,[b1])])
      else if   (a1 = a2 && (L.mem (b1,b2) ineq_params || L.mem (b2,b1) ineq_params))
             || (a1 = b2 && (L.mem (b1,a2) ineq_params || L.mem (a2,b1) ineq_params))
      then (binders, [(IR.one,[a1])])
      else (binders,fsp)
    | _ ->
      (binders,fsp)
  in

  let zparams = zero_params eq_constrs0 in
  let nzparams = nonzero_params ineq_constrs0 qineq_constrs0 in
  let eqparams = equal_params eq_constrs0 in
  let ineqparams = inequal_params qineq_constrs0 in

  F.printf "zero: %a\n" (pp_list ", " FS.pp_param) zparams;
  F.printf "nonzero: %a\n" (pp_list ", " FS.pp_param) nzparams;
  F.printf "equal: %a\n"
    (pp_list ", " (fun fmt (a,b) -> F.fprintf fmt "%a -> %a" FS.pp_param a FS.pp_param b))
    eqparams;
  F.printf "inequal: %a\n"
    (pp_list ", " (fun fmt (a,b) -> F.fprintf fmt "%a <> %a" FS.pp_param a FS.pp_param b))
    ineqparams;

  let simp_c c0 =
    let fs = [ (simp_zero zparams,"subst_zero"); (simp_nzero nzparams,"factor_nzero");
               (simp_equal eqparams,"subst_equal"); (simp_factor ineqparams,"factor_ineq") ]
    in
    let go (f,s) c =
      let c' = f c in
      if not (FS.equal_constr c c') then
        F.printf "simpl %s: %a ~~> %a\n" s (FS.pp_param_constr "=") c (FS.pp_param_constr "=") c';
      c'
    in
    L.fold_left (fun c f -> go f c) c0 fs
  in

  let eq_constrs = L.map simp_c eq_constrs0 in
  let ineq_constrs = L.map (L.map (simp_equal eqparams)) ineq_constrs0 in
  let qineq_constrs = qineq_constrs0 in

  if list_equal FS.equal_constr eq_constrs eq_constrs0 &&
     list_equal (list_equal FS.equal_constr) ineq_constrs ineq_constrs0 &&
     list_equal (list_equal FS.equal_constr) qineq_constrs qineq_constrs0
  then (eq_constrs0, ineq_constrs0, qineq_constrs0)
  else simp_constrs (sorted_nub FS. compare_constr eq_constrs) ineq_constrs qineq_constrs

(* \ic{Remove oracle outputs that are redundant because they can be computed from
       the oracle inputs and other outputs.} *)
let simp_gdef gdef =
  let is_param = function II.Param(_) -> true | _ -> false in
  let rec check xs ys =
    match xs,ys with
    | [], _ ->
      L.for_all is_param ys
    | x::xs, y::ys when x = y ->
      check xs ys
    | xs, y::ys when is_param y ->
      check xs ys
    | _ ->
      false
  in
  let computable_from k s =
    F.printf "Checking %a |- %a\n" II.OP.pp k II.OP.pp s;
    match II.OP.to_terms k, II.OP.to_terms s with
    | [(vks,ck)],[(vss,_cs)] when not (IR.equal ck IR.zero) ->
      check (L.sort compare vks) (L.sort compare vss)
    | _ -> false
  in
  let rec simp_orcl ls rs =
    match rs with
    | []    -> L.rev ls
    | r::rs ->
      if L.exists (fun l -> computable_from l r) ls
      then (F.printf "Dropped redundant oracle output %a\n" II.OP.pp r; simp_orcl ls rs)
      else simp_orcl (r::ls) rs
  in
  { gdef with
    II.gdef_odefs = List.map (fun (o,ops) -> (o, simp_orcl [] ops)) gdef.II.gdef_odefs }

let constr_unbound_idx (binders,fsp) =
  let bidxs = L.map fst binders in
  let idxs =
    conc_map
      (fun (_,ps) -> conc_map (function FS.OParam(_,i) | FS.OCoeff(_,_,_,i) -> [i] | _ -> []) ps)
      fsp
  in
  L.exists (fun i -> not (L.mem i bidxs)) idxs

(* \ic{Compute constraints for game definition.} *)
let gdef_to_constrs gdef =
  let gdef = simp_gdef gdef in
  let wcond = gdef.II.gdef_wcond in
  let eqs = wcond.II.wcond_eqs in
  let ineqs = wcond.II.wcond_ineqs in
  let gchoices =
    conc_map II.WP.vars (eqs@ineqs)
    |> L.map (function II.GroupChoice(v) -> Some(v) | _ -> None)
    |> catSome
    |> sorted_nub compare
    |> L.map (fun v -> (v, fs_of_gdef gdef v))
  in
  let oparams =
    conc_map
      (fun (o,ops) ->
         conc_map
           (fun op ->
              conc_map
                (function II.Param v -> [(v,o)] | _ -> [])
                (II.OP.vars op))
           ops)
      gdef.II.gdef_odefs
    |> sorted_nub compare
  in

  let is_oparam = function II.OParam(_) -> true | _ -> false in

  let qeqs, eqs = L.partition (fun wp -> L.exists is_oparam (II.WP.vars wp)) eqs in

  let qineqs, ineqs = L.partition (fun wp -> L.exists is_oparam (II.WP.vars wp)) ineqs in

  if qeqs <> [] then failwith "only inequality constraints allowed to contain oracle parameter";

  let wpoly_to_constr wp = wpoly_to_fs gchoices oparams wp |> FS.fs_to_constr in

  List.iter (fun e -> F.printf "@[%a@]\n\n" FS.pp_fsum (wpoly_to_fs gchoices oparams e)) eqs;

  let eq_constrs  = conc_map wpoly_to_constr eqs in
  let ineq_constrs = L.map wpoly_to_constr ineqs in

  if L.exists constr_unbound_idx (eq_constrs @ L.concat ineq_constrs) then
    failwith "Unbounded analysis failed (oracle returns monomial without freshly sampled random variable";

  let qwpoly_to_constr wp =
       wpoly_to_fs gchoices oparams wp
    |> FS.fs_to_constr
    |> L.map (fun (binders,fsp) ->
                if binders <> [] then failwith "impossible";
                let binders =
                  conc_map
                    (fun (_,ps) ->
                       conc_map
                         (function FS.OParam((_,o),i) -> [(i,o)] | _ -> [] )
                         ps)
                    fsp
                in (sorted_nub compare binders, fsp))
  in
  let qineq_constrs = L.map qwpoly_to_constr qineqs in

  let eq_constrs = eq_constrs |> L.map simp_constr |> sorted_nub FS.compare_constr in
  let ineq_constrs =
    ineq_constrs
    |> L.map (sorted_nub FS.compare_constr)
    |> sorted_nub (list_compare FS.compare_constr)
  in
  let qineq_constrs = qineq_constrs |> sorted_nub (list_compare FS.compare_constr) in

  simp_constrs eq_constrs ineq_constrs qineq_constrs


(* \ic{Compute constraints for game definition for bounded analysis.} *)
let gdef_to_constrs_bounded gdef =
  let gdef = simp_gdef gdef in
  let wcond = gdef.II.gdef_wcond in
  let eqs = wcond.II.wcond_eqs in
  let ineqs = wcond.II.wcond_ineqs in
  let gchoices =
    conc_map II.WP.vars (eqs@ineqs)
    |> L.map (function II.GroupChoice(v) -> Some(v) | _ -> None)
    |> catSome
    |> sorted_nub compare
    |> L.map (fun v -> (v, fs_of_gdef gdef v))
  in
  let oparams =
    conc_map
      (fun (o,ops) ->
         conc_map
           (fun op ->
              conc_map
                (function II.Param v -> [(v,o)] | _ -> [])
                (II.OP.vars op))
           ops)
      gdef.II.gdef_odefs
    |> sorted_nub compare
  in

  let is_oparam = function II.OParam(_) -> true | _ -> false in

  let qeqs, eqs = L.partition (fun wp -> L.exists is_oparam (II.WP.vars wp)) eqs in

  let _qineqs, ineqs = L.partition (fun wp -> L.exists is_oparam (II.WP.vars wp)) ineqs in

  if qeqs <> [] then failwith "only inequality constraints allowed to contain oracle parameter";

  let wpoly_to_constr wp = wpoly_to_fs gchoices oparams wp |> FS.fs_to_constr in

  List.iter (fun e -> F.printf "@[%a@]\n\n" FS.pp_fs_rvars (wpoly_to_fs gchoices oparams e |> FS.fs_to_fs_rvars)) eqs;

  let _eq_constrs  = conc_map wpoly_to_constr eqs in
  let _ineq_constrs = L.map wpoly_to_constr ineqs in

  exit 0
(*  
  if L.exists constr_unbound_idx (eq_constrs @ L.concat ineq_constrs) then
    failwith "Unbounded analysis failed (oracle returns monomial without freshly sampled random variable";

  let qwpoly_to_constr wp =
       wpoly_to_fs gchoices oparams wp
    |> FS.fs_to_constr
    |> L.map (fun (binders,fsp) ->
                if binders <> [] then failwith "impossible";
                let binders =
                  conc_map
                    (fun (_,ps) ->
                       conc_map
                         (function FS.OParam((_,o),i) -> [(i,o)] | _ -> [] )
                         ps)
                    fsp
                in (sorted_nub compare binders, fsp))
  in
  let qineq_constrs = L.map qwpoly_to_constr qineqs in

  let eq_constrs = eq_constrs |> L.map simp_constr |> sorted_nub FS.compare_constr in
  let ineq_constrs =
    ineq_constrs
    |> L.map (sorted_nub FS.compare_constr)
    |> sorted_nub (list_compare FS.compare_constr)
  in
  let qineq_constrs = qineq_constrs |> sorted_nub (list_compare FS.compare_constr) in

  (* (eq_constrs, ineq_constrs, qineq_constrs) *)
  simp_constrs eq_constrs ineq_constrs qineq_constrs
*)

(*********************************************************************)
(* \hd{Translation of constraints to JSON expressions} *)

let idx_of i = `String (F.sprintf "i%i" i)

let translate_param p =
  match p with
  | FS.FieldChoice(w)  ->
    `List [ `String "scalar"; `String ("fc_"^w) ]
  | FS.OParam((m,o),i) ->
    `List [ `String "app"; `String (F.sprintf "%s_%s_p" m o); idx_of i ]
  | FS.ICoeff(u,n)     ->
    `List [ `String "scalar"; `String (F.sprintf "%s_%i" u n) ]
  | FS.OCoeff(u,o,n,i) ->
    `List [ `String "app"; `String (F.sprintf "%s_%s_%i" u o n); idx_of i ]

let rec translate_prod ps =
  match ps with
  | []    -> `List [ `String "int"; `Int 1 ]
  | [p]   -> translate_param p
  | p::ps -> `List [ `String "mult"; translate_param p; translate_prod ps ]

let rec translate_sum (fsp : FS.fs_param) =
  match fsp with
  | [] ->
    `List [ `String "int"; `Int 0 ]
  | [(c,ps)] when IR.equal c IR.one ->
    translate_prod ps
  | [(c,ps)] ->
    `List [ `String "mult";
            `List [`String "int"; `Int (Big_int.int_of_big_int c)];
            translate_prod ps]
  | (c,ps)::ts when IR.equal c IR.one ->
    `List [ `String "add"; translate_prod ps; translate_sum ts ]
  | (c,ps)::ts ->
    `List [ `String "add";
            `List [ `String "mult";
                    `List [`String "int"; `Int (Big_int.int_of_big_int c)];
                    translate_prod ps];
            translate_sum ts ]

let rec translate_eq (binders,(fsp : FS.fs_param)) =
  match binders with
  | [] ->
    let pos, neg = L.partition (fun (c,_) -> IR.compare c IR.zero > 0) fsp in
    begin match neg with
    | [] ->
    `List [`String "eqz" ;translate_sum pos ]
    | _ -> 
    `List [`String "eq" ;translate_sum pos ; translate_sum (L.map (fun (c,ps) -> (IR.opp c,ps)) neg) ]
    end
  | (i,_o)::binders ->
    `List [ `String "forall"; idx_of i; translate_eq (binders,fsp) ]

let translate_ineq ineqs =
  let rec go ineqs = 
    match ineqs with
    | [] -> failwith "impossible"
    | [ineq] ->
      translate_eq ineq
    | ineq::ineqs ->
      `List [ `String "and"; translate_eq ineq; go ineqs]
  in
  `List [`String "not"; go ineqs ]


let rec translate_qineq qineqs =
  match qineqs with
  | [(binders,(fsp : FS.fs_param))] ->
    begin match binders with
    | [] ->
      let pos, neg = L.partition (fun (c,_) -> IR.compare c IR.zero > 0) fsp in
      `List [`String "not"; `List [`String "eq" ;translate_sum pos ; translate_sum (L.map (fun (c,ps) -> (IR.opp c,ps)) neg) ]]
    | (i,_o)::binders ->
      `List [ `String "forall"; idx_of i; translate_qineq [(binders,fsp)] ]
    end
  | _ -> failwith "impossible"


(*********************************************************************)
(* \hd{Unfolding formal sums given concrete bounds} *)



(*********************************************************************)
(* \hd{Parsing game definitions} *)

(* \ic{Convert lexer and parser errors to error with meaningful message.} *)
let wrap_error f s0 =
  let s = S.copy s0 in
  let sbuf = Lexing.from_string s0 in
  try
    f sbuf
  with
  | InteractiveParser.Error ->
    let start = Lexing.lexeme_start sbuf in
    let err =
      Printf.sprintf
        "Syntax error at offset %d (length %d): \
         parsed ``%s'',\nerror at ``%s''"
        start
        (S.length s)
        (if start >= S.length s then s  else (S.sub s 0 start))
        (if start >= S.length s then "" else (S.sub s start (S.length s - start)))
    in
    print_endline err;
    failwith err
  | InteractiveLexer.Error msg ->
    raise (failwith msg)

let p_cmds = wrap_error (InteractiveParser.cmds_t InteractiveLexer.lex)

(*********************************************************************)
(* \hd{Analyze game definitions} *)

let analyze_from_string s = 
  let gdef = p_cmds s |> II.eval_cmds in
  F.printf "%a\n\n" II.pp_gdef gdef;
  let eq_constrs, ineq_constrs, qineq_constrs = gdef_to_constrs_bounded gdef in
  List.iter (fun cs -> F.printf "%a\n" (FS.pp_param_constr "=") cs) eq_constrs;
  List.iter
    (fun cs -> F.printf "(%a)\n" (pp_list " \\/ " FS.pp_param_constr_ineq) cs)
    ineq_constrs;
  List.iter
    (fun cs -> F.printf "(%a)\n" (pp_list " \\/ " (FS.pp_param_constr "<>")) cs)
    qineq_constrs;

  (* exit 0 *)
  let pconstrs1 = sorted_nub compare (L.map translate_eq eq_constrs) in
  let pconstrs2 = sorted_nub compare (L.map translate_qineq qineq_constrs) in
  let pconstrs3 = sorted_nub compare (L.map translate_ineq ineq_constrs) in

  List.iter (fun pc -> print_endline (YS.to_string pc)) (pconstrs1 @ pconstrs2 @ pconstrs3);

  Z3_Solver.check_sat (pconstrs1 @ pconstrs2 @ pconstrs3)
  (* F.printf "%a\n" Z3_Solver.pp_result res *)
