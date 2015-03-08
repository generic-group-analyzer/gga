(*s Analyze non-parametric problem *)
(*i*)
open Util
open NonParamInput
open NonParamCompletion
open Poly
open Big_int

module S = String
(*i*)

(*******************************************************************)
(* \hd{Types for analysis} *)

(* \ic{Info for analysis of decisional problem.\\
   We use the same basis for all components.} *)
type dec_info = {
  di_gs         : closed_group_setting;
  di_inputs     : group_elem list * group_elem list;
  di_recipes    : recipe list;
  di_comp       : RP.t list list * RP.t list list;
  di_mbasis     : RP.monom list * RP.monom list;
  di_vcomp      : big_int list list * big_int list list;
  di_ker        : int list list *  int list list;
  di_attack     : (bool * int list) option;
}

(* \ic{Info for analysis of computational problem.\\
   We use the same basis for all components.} *)
type comp_info = {
  ci_gs         : closed_group_setting;
  ci_inputs     : group_elem list;
  ci_chal       : group_elem;
  ci_comp       : RP.t list list;
  ci_recipes    : recipe list;
  ci_mbasis     : RP.monom list;
  ci_vcomp      : big_int list list;
  ci_mmon_vchal : (RP.monom, big_int list) either;
  ci_attack     : (int list) option;
}

(* \ic{Analysis information.} *)
type info =
  | CompInfo of comp_info
  | DecInfo  of dec_info

(* \ic{Convenience constructor function.} *)
let mk_comp_info gs inputs chal comp recipes mbasis vcomp mv att = CompInfo {
  ci_gs         = gs;
  ci_inputs     = inputs;
  ci_chal       = chal;
  ci_comp       = comp;
  ci_recipes    = recipes;
  ci_mbasis     = mbasis;
  ci_vcomp      = vcomp;
  ci_mmon_vchal = mv;
  ci_attack     = att;
}

(* \ic{Convenience constructor function.} *)
let mk_dec_info gs inputs recipes comp mbasis vcomp ker att = DecInfo {
  di_gs      = gs;
  di_inputs  = inputs;
  di_recipes = recipes;
  di_comp    = comp;
  di_mbasis  = mbasis;
  di_vcomp   = vcomp;
  di_ker     = ker;
  di_attack  = att;
}

(* \ic{Result of analyzing an assumption} *)
type res =
  | Attack of info
  | Valid  of info * int

(*******************************************************************)
(* \hd{Analysis functions} *)

(* \ic{[get_vector_repr pss] returns the list of vector representations of
    of the lists polynomials [pss] with respect to the set of monomials occuring in [pss].
    It also returns the computed monomial basis.} *)
let get_vector_repr pss =
  let mbasis =
    conc_map (fun ps -> conc_map RP.mons ps) pss |>
      sorted_nub compare
  in
  let vps = L.map (fun ps -> conc_map (rp_to_vector mbasis) ps) pss in
  (mbasis, vps)

(* \ic{Analyze computational assumption by performning the following steps:
   \begin{enumerate}
   \item Compute completion of inputs for challenge group,
         compute monomial basis of completion, and
         compute vector representation of completion for
         this monomial basis.
   \item Check if the challenge contains monomials that are missing from the completion.
     If yes, the problem is hard unless the corresponding monomial vanishes modulo $p$.
   \item If no, we check if the corresponding linear system can be solved using Sage.
     Here, existence of a solution means that there is an attack.
     If there is no solution, then the problem is hard.
     {\bf FIXME:} For now, we don't track the bad primes in this case.
     We should use the same HNF + Kernel computation for [vchal] first line
     and [vcomp] matrix. Then only care about kernel elements where first line
     is used (we get [exc_ub] this way).\end{enumerate}} *)
let analyze_computational gs inputs chal =
  let (comp,recipes) = completion_for_group gs chal.ge_group inputs in
  let (mbasis,vcomp) = get_vector_repr comp in
  let missing_mons =
    conc_map
      (fun f ->
         conc_map
           (fun m -> if List.mem m mbasis then [] else [(m,RP.coeff f m) ])
           (RP.mons f))
      chal.ge_rpoly
  in
  let mk_info = mk_comp_info gs inputs chal comp recipes mbasis vcomp in
  match missing_mons with
  | (m,c)::_ -> Valid(mk_info (Left m) None, int_of_big_int c)
  | [] ->
    let vchal = conc_map (rp_to_vector mbasis) chal.ge_rpoly in
    let mk_info = mk_info (Right vchal) in
    begin match Sage_Solver.lin_solve vcomp vchal with
    | None      -> Valid(mk_info None, 1)
    | Some v    -> Attack(mk_info (Some v))
    end

(* \ic{Analyze decisional assumption by performning the following steps:
   \begin{enumerate}
   \item Compute completion of left and right inputs for target group,
         compute monomial basis of left and right completion, and
         compute vector representation of left and right completion for
         corresponding monomial basis.
   \item Build matrix (each row corresponds to polynomial) of left and right
     vector representation and compare the kernels using Sage.
   \item Result is either
       {\bf (a)} Kernels define the same subspace or
       {\bf (b)} there is element in left and not in right or vice versa.
       For the first case, we also give an upper bound on the primes $p$ for
       which the assumption might be invalid (e.g., because some term of
       the challenge or input polynomials vanishes modulo $p$).
       For the second case, we consider it sufficient that for each attack, there
       \emph{exists} a lower bound $b$ such that the attack is valid for all $p > b$.
   \end{enumerate}} *)
let analyze_decisional gs linp rinp =
  let (lcomp,rcomp,recipes) = completions_for_group gs gs.cgs_target linp rinp in
  let (lmb,lvcomp) = get_vector_repr lcomp in
  let (rmb,rvcomp) = get_vector_repr rcomp in
  let lk,rk,exc_ub,attacks = Sage_Solver.compare_kernel lvcomp rvcomp in
  let mk_info =
    mk_dec_info gs (linp,rinp) recipes (lcomp,rcomp) (lmb,rmb) (lvcomp,rvcomp) (lk,rk)
  in
  match (attacks : (bool * int list) list) with
  | []     -> Valid(mk_info None,exc_ub)
  | att::_ -> Attack(mk_info (Some(att)))

(* \ic{Analyze assumption.} *)
let analyze assm =
  match assm with
  | Computational(gs,inputs,chal)  -> analyze_computational gs inputs chal
  | Decisional(gs,linputs,rinputs) -> analyze_decisional gs linputs rinputs

(*******************************************************************)
(* \hd{Analyze assumption given as string or from file} *)

(* \ic{Convert lexer and parser errors to error with meaningful message.} *)
let wrap_error f s =
  let sbuf = Lexing.from_string s in
  try
    f sbuf
  with
  | NonParamParser.Error ->
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
  | NonParamLexer.Error msg ->
    raise (failwith (Printf.sprintf "%s" msg))
  | InvalidAssumption _ as e->
    raise e
  | _ ->
    failwith "Unknown error while lexing/parsing."

let p_cmds = wrap_error (NonParamParser.cmds_t NonParamLexer.lex)

let analyze_from_string scmds = scmds |> p_cmds |> eval_cmds |> analyze

let analyze_file fn = input_file fn |> analyze_from_string


(*i*)
(*******************************************************************)
(* \hd{Pretty printing} *)

let string_of_attack v recipes =
  let arecipe =
    L.concat
      (L.mapi
         (fun i a ->
            let sa = if a = 1 then "" else string_of_int a^"*" in
            if a = 0 then []
            else [ fsprintf "%s%a" sa pp_recipe (L.nth recipes i) ])
       v)
  in String.concat " + " arecipe

let pp_matrix fmt comp vcomp recipes =
  L.iter
    (fun (v,(f,r)) ->
       F.fprintf fmt "%a \t(%a using %a)\n" (pp_list "  \t" IntRing.pp) v pp_rp_vec f pp_recipe r)
    (L.combine vcomp (L.combine comp recipes))

let pp_ci fmt ci =
  F.fprintf fmt "\ninput:\n  %a\n" (pp_list "\n  " pp_group_elem) ci.ci_inputs;
  F.fprintf fmt "\ncompletion (for group %a):\n" pp_group_id ci.ci_chal.ge_group;
  F.fprintf fmt "%a \t(monomial basis)\n" (pp_list " \t" RP.pp_monom) ci.ci_mbasis;
  pp_matrix fmt ci.ci_comp ci.ci_vcomp ci.ci_recipes;
  match ci.ci_mmon_vchal with
  | Left m ->
    F.fprintf fmt "\nMonomial %a occurs only in challenge and not in completion\n" RP.pp_monom m
  | Right vchal ->
    F.fprintf fmt "\nchallenge vector:\n";
    F.fprintf fmt "%a \t(monomial basis)\n" (pp_list " \t" RP.pp_monom) ci.ci_mbasis;
    F.fprintf fmt "%a \t(%a)\n" (pp_list "  \t" IntRing.pp) vchal pp_rp_vec ci.ci_chal.ge_rpoly

let pp_di fmt di =
  let exp_basis b = L.concat (replicate b di.di_gs.cgs_prime_num) in
  let (cinp, linp, rinp) = common_prefix equal_group_elem (fst di.di_inputs) (snd di.di_inputs) in
  F.fprintf fmt "\ncommon input:\n  %a\n" (pp_list "\n  " pp_group_elem)  cinp;
  F.fprintf fmt "\ninput left:\n  %a\n"   (pp_list "\n  " pp_group_elem)  linp;
  F.fprintf fmt "\ninput right:\n  %a\n"  (pp_list "\n  " pp_group_elem)  rinp;

  F.fprintf fmt "\ncompletion left (for group %a):\n" pp_group_id di.di_gs.cgs_target;
  F.fprintf fmt "%a \t(monomial basis)\n" (pp_list " \t" RP.pp_monom) (exp_basis (fst di.di_mbasis));
  pp_matrix fmt (fst di.di_comp) (fst di.di_vcomp) di.di_recipes;

  F.fprintf fmt "\ncompletion right (for group %a):\n" pp_group_id di.di_gs.cgs_target;
  F.fprintf fmt "%a \t(monomial basis)\n" (pp_list " \t" RP.pp_monom) (exp_basis (snd di.di_mbasis));
  pp_matrix fmt (snd di.di_comp) (snd di.di_vcomp) di.di_recipes;

  if fst di.di_ker = [] && fst di.di_ker = [] then F.fprintf fmt "No equalities on left or right";
  if fst di.di_ker <> [] then
    F.fprintf fmt "\nbasis for equalities left:\n%a\n"  (pp_list "\n" (pp_list "  \t" pp_int)) (fst di.di_ker);
  if snd di.di_ker <> [] then
    F.fprintf fmt "\nbasis for equalities right:\n%a\n" (pp_list "\n" (pp_list "  \t" pp_int)) (snd di.di_ker)

let pp_info fmt info =
  match info with
  | CompInfo ci -> pp_ci fmt ci
  | DecInfo di  -> pp_di fmt di

let pp_result_info fmt res =
  match res with
  | Valid(info,_) | Attack(info) -> pp_info fmt info

let pp_result fmt res =
  match res with
  | Valid(_,eub) ->
    F.fprintf fmt "The assumption is valid for all primes%s."
      (if eub = 1 then "" else " > "^string_of_int eub)
  | Attack(info) ->
    F.fprintf fmt "There is an attack: ";
    (match info with
     | DecInfo di ->
         begin match di.di_attack with
         | None            -> assert false
         | Some(is_left,v) ->
           F.fprintf fmt "The equality '%s = 0' holds on the %s, but not on the %s."
             (string_of_attack v di.di_recipes)
             (if is_left then "left"  else "right")
             (if is_left then "right" else "left")
         end
     | CompInfo ci ->
       begin match ci.ci_attack with
       | None    -> assert false
       | Some(v) ->
         F.fprintf fmt "The challenge can be computed using %s."
             (string_of_attack v ci.ci_recipes)
       end)
(*i*)
