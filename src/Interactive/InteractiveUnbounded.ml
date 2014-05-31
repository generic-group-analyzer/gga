(*s Unbounded analysis for interactive assumptions. *)

(*i*)
open Util
open Poly

module FS = InteractiveFormalSum
module IR = IntRing
module II = InteractiveInput
module S = String

module YS = Yojson.Safe
(*i*)

(*********************************************************************)
(* \hd{Validity checking for game definitions and constraints} *)

(* \ic{Check if there are unbound index variables in given constraint.
       These arise, e.g., from oracles that return polynomials
       containing momonials without freshly sampled random
       variables.} *)
let constr_unbound_idx (binders,fsp) =
  let bidxs = L.map fst binders in
  let idxs =
    conc_map
      (fun (_,ps) -> catSome (L.map FS.db_idx_of_param ps) |> L.map fst)
      fsp
  in
  L.exists (fun i -> not (L.mem i bidxs)) idxs

let gdef_wcond_groupchoice gdef =
  let is_gchoice = function II.GroupChoice(_) -> true | _ -> false in
  let wcond = gdef.II.gdef_wcond in
  let eqs   = wcond.II.wcond_eqs in
  let ineqs = wcond.II.wcond_ineqs in
  let bad_wcond wp =
    L.exists
      (fun (vs,_) -> L.length (L.filter is_gchoice vs) > 1)
      (II.WP.to_terms wp)
  in
  L.exists bad_wcond (eqs@ineqs)

let gdef_oracle_no_rvar gdef =
  let not_orvar = function II.ORVar(_) -> false | _ -> true in
  let bad_op op = L.exists (fun (vs,_) -> L.for_all not_orvar vs) (II.OP.to_terms op) in
  L.exists (fun (_,ops) -> L.exists bad_op ops) gdef.II.gdef_odefs

(*********************************************************************)
(* \hd{Constraint simplification} *)

let is_one c = IR.equal c IR.one

let is_minus_one c = IR.equal c (IR.opp IR.one)

let is_zero c = IR.equal c IR.zero

(* \ic{Return parameters for which constraints imply that they are zero.} *)
let zero_params eq_constrs =
  conc_map (function (_,[(c,[p])]) when not (is_zero c) -> [p] | _ -> []) eq_constrs

(* \ic{Return equalities between parameters implied by constraints.} *)
let equal_params eq_constrs =
  let go (_,fsp) =
    let pos, neg = L.partition (fun (c,_) -> IR.compare c IR.zero > 0) fsp in
    begin match pos, neg with
    | [(c1,[p1])], [(c2,[p2])] when is_one c1 && is_minus_one c2 ->
      let cmp = compare p1 p2 in
      if  cmp > 0 then [(p1,p2)] else if cmp < 0 then [(p2,p1)] else []
    | _ ->
      []
    end
  in
  conc_map go eq_constrs

(* \ic{Return inequalities between parameters implied by constraints.} *)
let inequal_params qineq_constrs =
  let go c =
    match c with
    | [(_,fsp)] ->
      let pos, neg = L.partition (fun (c,_) -> IR.compare c IR.zero > 0) fsp in
      begin match pos, neg with
      | [(c1,[p1])], [(c2,[p2])] when is_one c1 && is_minus_one c2 ->
        let cmp = compare p1 p2 in
        if cmp > 0 then [(p1,p2)] else if cmp < 0 then [(p2,p1)] else []
      | _ ->
        []
      end
    | _ ->
      []
  in
  conc_map go qineq_constrs

(* \ic{Return parameters for which constraints that they are non-zero.} *)
let nonzero_params ineq_constrs qineq_constrs =
  (conc_map
     (function [(_,[(c,[p])])] when not (is_zero c) -> [p] | _ -> [])
     qineq_constrs)
  @
  (conc_map
     (function [([],[(c,[p])])] when not (is_zero c) -> [p] | _ -> [])
     ineq_constrs)

(* \ic{Simplify using $ -1 * a + (-1)*b = 0 \Leftrightarrow a + b = 0$. } *)  
let simp_negate (binders,fsp) =
  match fsp with
  | _ when L.for_all (fun (c,_) -> is_minus_one c) fsp ->
    (binders,L.map (fun (_,ps) -> (IR.one,ps)) fsp)
  | _ ->
    (binders,fsp)

(* \ic{Simplify using $a = 0 \land a * b + c = 0 \Rightarrow c = 0$. } *)  
let simp_zero zparams (binders,fsp) =
  let fsp' = L.filter (fun (_c,ps) -> not (L.exists (fun p -> L.mem p zparams) ps)) fsp in
  if L.length fsp' > 0 then (binders,fsp') else (binders,fsp)

(* \ic{Simplify using $a \neq 0 \land a * b = 0 \Rightarrow b = 0$. } *)  
let simp_nzero nzparams (binders,fsp) =
  match fsp with
  | [(c,ps)] ->
    let ps' = L.filter (fun p -> not (L.mem p nzparams)) ps in
    if L.length ps' > 0 then (binders,[(c,ps')]) else (binders,[(c,ps)])
  | _        ->
    (binders,fsp)

(* \ic{Simplify using equalities to replace equals by equals. } *)
let simp_equal eq_params (binders,fsp) =
  (binders, L.map (fun (c,ps) ->
                     (c,L.map (fun p -> try (L.assoc p eq_params) with Not_found -> p) ps))
                  fsp)

(* \ic{Simplify using $a*c = a * d \land c \neq d \Rightarrow a = 0$. } *)
let simp_factor ineq_params (binders,fsp) =
  let is_ineq p1 p2 = L.mem (p1,p2) ineq_params || L.mem (p2,p1) ineq_params in
  let pos, neg = L.partition (fun (c,_) -> IR.compare c IR.zero > 0) fsp in
  match pos, neg with
  | [(c1,[a1;b1])], [(c2,[a2;b2])] when is_one c1 && is_minus_one c2 ->
    if   (b1 = b2 && is_ineq a1 a2) || (b1 = a2 && is_ineq a1 b2)
    then (binders, [(IR.one,[b1])])
    else if (a1 = a2 && is_ineq b1 b2) || (a1 = b2 && is_ineq b1 a2)
    then (binders, [(IR.one,[a1])])
    else (binders,fsp)
  | _ ->
    (binders,fsp)

(* \ic{Simplify given constraints until fixpoint is reached. } *)  
let rec simp_constrs eq_constrs0 ineq_constrs0 qineq_constrs0 =

  (* \ic{Sort and remove duplicate constraints.} *)
  let eq_constrs = sorted_nub FS.compare_constr eq_constrs0 in
  let ineq_constrs =
    ineq_constrs0
    |> L.map (sorted_nub FS.compare_constr)
    |> sorted_nub (list_compare FS.compare_constr)
  in
  let qineq_constrs =
    qineq_constrs0
    |> L.map (sorted_nub FS.compare_constr)
    |> sorted_nub (list_compare FS.compare_constr)
  in

  let zparams = zero_params eq_constrs in
  let nzparams = nonzero_params ineq_constrs qineq_constrs in
  let eqparams = equal_params eq_constrs in
  let ineqparams = inequal_params qineq_constrs in

  (*i
  F.printf ">> zero variables: %a\n" (pp_list ", " FS.pp_param) zparams;
  F.printf ">> nonzero variables: %a\n" (pp_list ", " FS.pp_param) nzparams;
  F.printf ">> equalities: %a\n" (pp_list ", " (pp_tuple " = " FS.pp_param)) eqparams;
  F.printf ">> inequalities: %a\n" (pp_list ", " (pp_tuple " <> " FS.pp_param)) ineqparams;
  i*)

  let simp_constr c0 =
    let fs =
      [ (simp_negate, "negate")
      ; (simp_zero zparams,"subst_zero")
      ; (simp_nzero nzparams,"factor_nzero")
      ; (simp_equal eqparams,"subst_equal")
      ; (simp_factor ineqparams,"factor_ineq") ]
    in
    let go (f,s) c =
      let c' = f c in
      if not (FS.equal_constr c c') then
        F.printf "simpl %s: %a ~~> %a\n" s (FS.pp_param_constr "=") c (FS.pp_param_constr "=") c';
      c'
    in
    L.fold_left (fun c f -> go f c) c0 fs
  in

  let eq_constrs = L.map simp_constr eq_constrs in
  let ineq_constrs = L.map (L.map (simp_equal eqparams)) ineq_constrs in

  if list_equal FS.equal_constr eq_constrs eq_constrs0 &&
     list_equal (list_equal FS.equal_constr) ineq_constrs ineq_constrs0 &&
     list_equal (list_equal FS.equal_constr) qineq_constrs qineq_constrs0
  then (eq_constrs0, ineq_constrs0, qineq_constrs0)
  else simp_constrs eq_constrs ineq_constrs qineq_constrs

(*********************************************************************)
(* \hd{Analyze game definitions} *)

let pp_constrs fmt eq_constrs ineq_constrs qineq_constrs =
  List.iter (fun cs -> F.fprintf fmt "%a\n" (FS.pp_param_constr "=") cs) eq_constrs;
  List.iter
    (fun cs -> F.fprintf fmt "(%a)\n" (pp_list " \\/ " FS.pp_param_constr_ineq) cs)
    ineq_constrs;
  List.iter
    (fun cs -> F.fprintf fmt "(%a)\n" (pp_list " \\/ " (FS.pp_param_constr "<>")) cs)
    qineq_constrs


(* \ic{Compute formal sum for group choice [gchoice] and [gdef].} *)
let fs_of_gdef gdef gchoice =
  let inputs = gdef.II.gdef_inputs in
  let odefs = gdef.II.gdef_odefs in
  FS.(

    (* \ic{Linear combination of adversary inputs.} *)
    let conv_term_inp n (m,c) = (c, [ICoeff(gchoice,n)], L.map (fun v -> SRVar v) m) in
    let f1 =
      zip_indices inputs
      |> conc_map (fun (n,f) -> L.map (conv_term_inp n) (II.RP.to_terms f)) 
    in

    (* \ic{Linear combination for $n$-th output of oracle $o$.} *)
    let conv_term_orcl o n (m,c) =
      (c
      , OCoeff(gchoice,o,n,0)
        ::(conc_map (function II.Param(id) -> [OParam((id,o),0)] | _ -> []) m)
      , conc_map
          (function II.SRVar(v) -> [SRVar(v)] | II.ORVar(v) -> [ORVar((v,o),0)] | _ -> [])
          m
      )
    in
    let lincomb o n f = L.map (conv_term_orcl o n) (II.OP.to_terms f) in
    let comb_orcl (o,fs) = conc_map (fun (n,f) -> lincomb o n f) (zip_indices fs) in
    let fos = conc_map comb_orcl odefs in
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

(* \ic{Compute constraints for game definition.} *)
let gdef_to_constrs gdef =
  let gdef = II.simp_gdef gdef in
  if gdef_oracle_no_rvar gdef then
    failwith ("Unbounded verification restricted to oracles where "^
              "all monomials in returned polynomials must contain at "^
              "least one random variable sampled in oracle.");
  if gdef_wcond_groupchoice gdef then
    failwith ("Unbounded verification restricted to winning conditions "^
              "that do not contain products of group elements chosen by "^
              "adversary.");

  let wcond = gdef.II.gdef_wcond in
  let eqs = wcond.II.wcond_eqs in
  let ineqs = wcond.II.wcond_ineqs in
  let odefs = gdef.II.gdef_odefs in

  let gchoices =
    L.map (fun v -> (v, fs_of_gdef gdef v)) (II.gchoices_of_gdef gdef)
  in

  (* \ic{Mapping from oracle parameter to oracle name.} *)
  let oparams =
    conc_map
      (fun (o,ops) ->
         conc_map
           (fun op ->
              conc_map
                (function II.Param v -> [(v,o)] | _ -> [])
                (II.OP.vars op))
           ops)
      odefs
    |> sorted_nub compare
  in

  let is_oparam = function II.OParam(_) -> true | _ -> false in

  let qeqs, eqs = L.partition (fun wp -> L.exists is_oparam (II.WP.vars wp)) eqs in

  let qineqs, ineqs = L.partition (fun wp -> L.exists is_oparam (II.WP.vars wp)) ineqs in

  if qeqs <> [] then
    failwith "only inequality constraints allowed to contain oracle parameter";

  let wpoly_to_constr wp = wpoly_to_fs gchoices oparams wp |> FS.fs_to_constr in

  F.printf "#########################################################\n";

  F.printf "Winning conditions:\n";
  F.printf "(for the chosen group element U in the winning condition, we use\n";
  F.printf " U_I_j for the coefficient of the j-th adversary input and\n";
  F.printf " U_O_j_i0 for the coefficient of the j-th oracle output in the i0-th query)\n\n";

  List.iter
    (fun e ->
       F.printf "@[0 = @.  %a@]\n\n"
         FS.pp_fs_rvars
         (wpoly_to_fs gchoices oparams e |> FS.fs_to_fs_rvars))
    eqs;

  List.iter
    (fun e ->
       F.printf "@[0 <> @.  %a@]\n\n"
         FS.pp_fs_rvars
         (wpoly_to_fs gchoices oparams e |> FS.fs_to_fs_rvars))
    ineqs;

  List.iter
    (fun e ->
       F.printf "@[forall i0: 0 <> %a@]\n\n"
         FS.pp_fs_rvars
         (wpoly_to_fs gchoices oparams e |> FS.fs_to_fs_rvars))
    qineqs;

  let eq_constrs  = conc_map wpoly_to_constr eqs in
  let ineq_constrs = L.map wpoly_to_constr ineqs in

  if L.exists constr_unbound_idx (eq_constrs @ L.concat ineq_constrs) then
    failwith "impossible: free index variable";

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

  F.printf "\n#########################################################\n";
  F.printf "Initial constraints:\n\n";
  pp_constrs F.std_formatter eq_constrs ineq_constrs qineq_constrs;
  print_newline ();

  simp_constrs eq_constrs ineq_constrs qineq_constrs

(*********************************************************************)
(* \hd{Translation of constraints to JSON expressions} *)

let idx_of i = `String (F.sprintf "i%i" i)

let translate_param p =
  match p with
  | FS.FieldChoice(w)  ->
    `List [ `String "scalar"; `String ("fc_"^w) ]
  | FS.OParam((m,o),i) ->
    `List [ `String "app"; `String (F.sprintf "%s_%s_p" m o); idx_of i ]
  | FS.ICoeff(u,n) ->
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
    | []          -> failwith "impossible"
    | [ineq]      -> translate_eq ineq
    | ineq::ineqs -> `List [ `String "and"; translate_eq ineq; go ineqs]
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
