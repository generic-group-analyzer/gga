(*s Input for interactive assumptions. We assume that there is only one group for now,
    i.e., the setting is equivalent to the generic group setting.
%  
       Note that this is the case for most computational problems where
       a bilinear map that does not occur in the input, oracle, and
       winning definition is useless. *)
(*i*)
open Util
open Poly
open StringPoly
open Printf
(*i*)

exception InvalidAssumption of string

(*******************************************************************)
(* \hd{Adversary input definition} *)

(* \ic{For the adversary input, we use polynomials in $\ZZ[\vec{X}]$
       for random variables $\vec{X}$.} *)

type rvar_id = string

module RP = SP

type rpoly = RP.t

(*******************************************************************)
(* \hd{Oracle definition} *)

(* \ic{For the oracle return values, we use polynomials in
       $\ZZ[\vec{X},\vec{A},\vec{m}]$ where
       $\vec{X}$ are shared (initially sampled) random variables,
       $\vec{A}$ are random variables sampled in the oracle,
       $\vec{m}$ are oracle arguments in $\field$.
       The oracle is then implicitly defined as follows by such a vector of polynomials $\vec{f}$:\\
       Take (named) parameters $\vec{m} = params(\vec{f})$ as inputs,
       sample $\vec{A} = freshvars(\vec{f})$ in $\group$,
       return $(f_1(\vec{X}, \vec{A}, \vec{m}),\ldots,
                f_{|\vec{f}|}(\vec{X}, \vec{A}, \vec{m}))$.} *)
type oparam_id = string
type ofparam_id = string
type ohparam_id = string
type orvar_id = string

(* \ic{Variables in oracle polynomials.} *)
type ovar = 
  | FParam of ofparam_id
  | HParam  of ohparam_id 
  | SRVar of rvar_id
  | ORVar of orvar_id

let string_of_ovar v = match v with
  | FParam s | HParam s | SRVar s | ORVar s -> s

(*i*)
let pp_ovar fmt v = pp_string fmt (string_of_ovar v)
(*i*)

(* \ic{Oracle polynomials.} *)
module OP = MakePoly(struct
  type t = ovar
  let pp = pp_ovar
  let equal = (=)
  let compare = compare
end) (IntRing)

type opoly = OP.t

(* \ic{An oracle definition is just a list of oracle polynomials
       using the interpretation given above.} *)
type odef = opoly list

(*i*)
let pp_opoly fmt opolys =
  let get_fparam v = match v with FParam s -> [s] | _ -> [] in
  let get_hparam v = match v with HParam s -> [s] | _ -> [] in
  let get_orvar  v = match v with ORVar s -> [s] | _ -> [] in
  let fparams =
    conc_map (fun f -> conc_map get_fparam (OP.vars f)) opolys
    |> sorted_nub compare
  in
  let hparams =
    conc_map (fun f -> conc_map get_hparam (OP.vars f)) opolys
    |> sorted_nub compare
  in
  let orvars =
    conc_map (fun f -> conc_map get_orvar (OP.vars f)) opolys
    |> sorted_nub compare
  in
  F.fprintf fmt "(%a%s%a) = %a; return (%a)"
    (pp_list ", " (fun fmt -> F.fprintf fmt "%s:Fq")) fparams
    (if fparams = [] then "" else ", ")
    (pp_list ", " (fun fmt -> F.fprintf fmt "%s:G")) hparams
    (pp_list "; " (fun fmt -> F.fprintf fmt "%s <-$ G")) orvars
    (pp_list ", " OP.pp) opolys
(*i*)

(*******************************************************************)
(* \hd{Winning condition definition} *)

(* \ic{A winning condition is given by two sets of polynomials,
   one set that is interpreted as the required equalities and one set
   interpreted as the required inequalities.
   These polynomials are in $\ZZ[\vec{X},\vec{U},\vec{w},\vec{m}]$
   where $\vec{X}$ denotes the random variables, $\vec{U}$ denotes the
   adversary choices in $\group$, $\vec{w}$ denotes the adversary choices
   in $\field$, and $\vec{m}$ denotes the oracle arguments.
   Every inequality (resp. equality) polynomial containing oracle argument
   variables~$m$ is interpreted as
   $\forall i \in [q]: f(\ldots,m_i,\ldots) \neq 0$ (resp. $=$).} *)

type gchoice_id = string
type fchoice_id = string

(* \ic{Variables in winning condition polynomials.} *)
type wvar = 
  | GroupChoice of gchoice_id
  | FieldChoice of fchoice_id
  | OFParam     of ofparam_id
  | OHParam     of ohparam_id
  | RVar        of rvar_id

(*i*)
let string_of_wvar v = match v with
  | GroupChoice s | FieldChoice s | RVar s -> s
  | OFParam s | OHParam s-> s^"_i"

let pp_wvar fmt v = pp_string fmt (string_of_wvar v)
(*i*)

(* \ic{Winning condition polynomials.} *)
module WP = MakePoly(struct
  type t = wvar
  let pp = pp_wvar
  let equal = (=)
  let compare = compare
end) (IntRing)

type wpoly = WP.t

(*i*)
let pp_wpoly fmt wp =
  if L.exists (function OFParam _ -> true | _ -> false) (WP.vars wp) then
    F.fprintf fmt "forall i: %a" WP.pp wp
  else
    WP.pp fmt wp
(*i*)

(* \ic{A winning condition consists of a list of equalities and a list
       of inequalities.} *) 
type wcond = {
  wcond_eqs   : wpoly list;
  wcond_ineqs : wpoly list;
}

(*i*)
let pp_eq fmt = F.fprintf fmt "%a = 0" pp_wpoly

let pp_ineq fmt = F.fprintf fmt "%a <> 0" pp_wpoly

let pp_wcond_conds fmt wcond =
  let pp_eqs = pp_list " /\\ " pp_eq in
  let pp_ineqs = pp_list " /\\ " pp_ineq in
  match wcond.wcond_eqs, wcond.wcond_ineqs with
  | [], []     -> F.fprintf fmt "true"
  | eqs, []    -> F.fprintf fmt "%a" pp_eqs eqs
  | [], ineqs  -> F.fprintf fmt "%a" pp_ineqs ineqs
  | eqs, ineqs -> F.fprintf fmt "%a /\\ %a" pp_eqs eqs pp_ineqs ineqs

let pp_wcond fmt wcond =
  let fold_vars g =
    wcond.wcond_eqs @ wcond.wcond_ineqs
    |> conc_map (fun f -> conc_map g (WP.vars f))
    |> sorted_nub compare
  in
  let pp_ty_list ty fmt ns =
    pp_list ", " pp_string fmt (L.map (fun n -> n^":"^ty) ns)
  in
  let pp_args fmt (gchoices,fchoices) = match gchoices, fchoices with
    | [], [] -> F.fprintf fmt ""
    | [], _  -> pp_ty_list "G" fmt gchoices
    | _, []  -> pp_ty_list "G" fmt gchoices
    | _, _   -> F.fprintf fmt "%a, %a" (pp_ty_list "G")  gchoices (pp_ty_list "Fq") fchoices
  in
  let gchoices = fold_vars (function GroupChoice v -> [v] | _ -> []) in
  let fchoices = fold_vars (function FieldChoice v -> [v] | _ -> []) in
  F.fprintf fmt "win (%a) = ( %a )."
    pp_args (gchoices, fchoices)
    pp_wcond_conds wcond
(*i*)

(*******************************************************************)
(* \hd{Game definition} *)

type oname = string

(* \ic{A game definition consists of the adversary input,
       the definition of (named) oracles, and
       the definition of the winning condition.} *)
type gdef = {
  gdef_inputs : rpoly list;
  gdef_odefs  : (oname * odef) list;
  gdef_wcond  : wcond;
}

(* \ic{Remove oracle outputs that are redundant because they can be computed from
       the oracle inputs and other outputs.} *)
let simp_gdef gdef =
  let is_param = function FParam(_) -> true | _ -> false in
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
    match OP.to_terms k, OP.to_terms s with
    | [(vks,ck)],[(vss,_cs)] when not (IntRing.equal ck IntRing.zero) ->
      check (L.sort compare vks) (L.sort compare vss)
    | _ -> false
  in
  let rec simp_orcl ls rs =
    match rs with
    | []    -> L.rev ls
    | r::rs ->
      if L.exists (fun l -> computable_from l r) ls
      then simp_orcl ls rs
      else simp_orcl (r::ls) rs
  in
  { gdef with
    gdef_odefs = List.map (fun (o,ops) -> (o, simp_orcl [] ops)) gdef.gdef_odefs }

let gchoices_of_gdef gdef =
  let eqs = gdef.gdef_wcond.wcond_eqs in
  let ineqs = gdef.gdef_wcond.wcond_ineqs in  
  conc_map WP.vars (eqs@ineqs)
  |> L.map (function GroupChoice(v) -> Some(v) | _ -> None)
  |> catSome
  |> sorted_nub compare


(*i*)
let pp_gdef fmt gdef =
  F.fprintf fmt "input [%a] in G.\n\n%a\n\n%a"
    (pp_list ", " RP.pp) gdef.gdef_inputs
    (pp_list "\n" (fun fmt (n,o) -> F.fprintf fmt "oracle %s%a." n pp_opoly o))
        gdef.gdef_odefs
    pp_wcond gdef.gdef_wcond
(*i*)

(*******************************************************************)
(* \hd{Commands to define games} *)

type ty = Group | Field

type cond_type = Eq | InEq

(* \ic{We use [rpoly]s for all types of commands and convert later on when
       we have all information required to distinguish the different types
       of variables.} *)
type cmd =
  | AddInput   of rpoly list
  | AddOracle  of oname * (oparam_id * ty) list * orvar_id list * rpoly list
  | SetWinning of (oparam_id * ty) list * (rpoly * cond_type) list

(*i*)
let pp_cmd fmt cmd =
  let ty_to_string = function Group -> "G" | Field -> "Fp" in
  let cty_to_string = function Eq -> " = 0" | InEq -> " <> 0" in
  match cmd with
  | AddInput fs ->
    F.fprintf fmt "add_input %a" (pp_list "," RP.pp) fs
  | AddOracle(s,params,orvars,fs) ->
    F.fprintf fmt "add_oracle %s(%a) sample %a; (%a)" s
      (pp_list ", " (fun fmt (s,ty) -> pp_string fmt (s^":"^ty_to_string ty))) params
      (pp_list ", " pp_string) orvars
      (pp_list ", " RP.pp) fs
  | SetWinning(choices,conds) ->
    F.fprintf fmt "set_winning (%a) cond: %a"
      (pp_list ", "
         (fun fmt (s,ty) -> pp_string fmt (s^":"^ty_to_string ty)))
      choices
      (pp_list " /\\ "
         (fun fmt (f,cty) -> F.fprintf fmt "%a%s" RP.pp f (cty_to_string cty)))
      conds
(*i*)

let rpoly_to_opoly _gvars params orvars p =
  let fparams = List.map fst (List.filter (fun (_, t) -> t = Field) params) in
  let hparams = List.map fst (List.filter (fun (_, t) -> t = Group) params) in
  let conv_var v =
    if L.mem v fparams then FParam(v)
    else if L.mem v hparams then HParam(v) 
    else if L.mem v orvars then ORVar(v)
    else SRVar(v)
    (*i 
    else if L.mem v gvars then 
    else failwith ("undefined variables in oracle definition: "^v)
    i*)
  in
(*  printf "\nField vars:\n";
  List.iter (printf "%s") fvars;
  printf "\nGroup vars:\n";
  List.iter (printf "%s") hvars; *)
  RP.to_terms p
  |> L.map (fun (m,c) -> (L.map conv_var m, c))
  |> OP.from_terms

let rpoly_to_wpoly _gvars choices oparams p =
  let fchoices = conc_map (function (v,Field) -> [v] | _ -> []) choices in
  let gchoices = conc_map (function (v,Group) -> [v] | _ -> []) choices in
  let has_group_choice = ref false in
  let has_oparam       = ref false in  
  let conv_var v =
    if L.mem v oparams then (has_oparam := true; OFParam(v))
    else if L.mem v fchoices then FieldChoice(v)
    else if L.mem v gchoices then (has_group_choice := true; GroupChoice(v))
    else RVar(v)
    (*i
    else if L.mem v gvars    then RVar(v)
    else failwith ("undefined variables in winning condition definition: "^v)
    i*)
  in
  if !has_oparam && !has_group_choice then
    failwith "Polynomials that contain both oracle parameter and group choice not supported";
  RP.to_terms p
  |> L.map (fun (m,c) -> (L.map conv_var m, c))
  |> WP.from_terms

let eval_cmd (inputs0,odefs0,oparams0,orvars0,mwcond0) cmd =
  let gvars = conc_map (fun f -> RP.vars f) inputs0 |> sorted_nub compare in
  match cmd,mwcond0 with
  | AddInput fs, None ->
    ( inputs0@fs
    , odefs0
    , oparams0
    , orvars0
    , mwcond0
    )
  | AddOracle(oname,params,orvars,fs), None ->
    if (L.length params <> L.length (sorted_nub compare (L.map fst params)))
      then failwith "Two arguments with the same name in oracle definition";
    if (L.length orvars <> L.length (sorted_nub compare orvars))
      then failwith "Oracle samples two random variables with the same name";
    if L.exists (fun (oname',_) -> oname = oname') odefs0
      then failwith ("Oracle name used twice: "^oname);
    F.printf "%a\n" pp_cmd cmd;
    ( inputs0
    , odefs0@[ (oname, L.map (rpoly_to_opoly gvars params orvars) fs) ]
    , oparams0@( L.map fst params )
    , orvars0@orvars
    , None
    )
  | SetWinning(choices,conds), None ->
    let conv = rpoly_to_wpoly gvars choices oparams0 in
    let ineqs = conc_map (function (f,InEq) -> [ conv f ] | (_,Eq)   -> []) conds in
    let eqs   = conc_map (function (f,Eq)   -> [ conv f ] | (_,InEq) -> []) conds in
    ( inputs0
    , odefs0
    , oparams0
    , orvars0
    , Some { wcond_ineqs = ineqs; wcond_eqs = eqs }
    )
  | _, Some _ ->
    failwith "Setting the winning condition must be the last command"

let eval_cmds cmds =
  match List.fold_left eval_cmd ([], [], [], [], None) cmds with
  | (_, _, _, _, None)   ->
    failwith "no winning condition given"
  | (inputs, odefs, _, _, Some wcond) ->
    { gdef_inputs = inputs; gdef_odefs = odefs; gdef_wcond = wcond }
