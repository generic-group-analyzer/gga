(* This file is distributed under the MIT License (see LICENSE). *)

(*i*)
open Util
open Poly

module IR = IntRing
module II = IUnboundedInput
module S = String
(*i*)

(*********************************************************************)
(* \hd{Formal sum: types} *)

(* \ic{We use formal sums to represent linear combinations of
       adversary inputs and oracle return values and their products and
       sums.} *)

(* \ic{De Bruin index for index variables.} *)
type db_idx = int

(* \ic{Index of adversary input, e.g., $i$-th element of list given to adversary.} *)
type input_idx = int

(* \ic{Index of return value, e.g., $i$-th element of list returned by oracle.} *)
type oreturn_idx = int

(* \ic{We combine the name of the random variable with the oracle name for uniqueness.} *)
type orvar_id = II.orvar_id * II.oname

(* \ic{We combine the name of the oracle parameter with the oracle name for uniqueness.} *)
type oparam_id = II.oparam_id * II.oname

(* \ic{Formal sums use index variables $i_1$, $i_2$, $\ldots$ and are built from
    variables in
   \begin{description}
   \item [SRVar(X)]${}=X$: shared random variable $X$ used in adversary input.
   \item [ORVar((A,o),j)] ${}=A^o_{i_j}$: random variable $A$ sampled in oracle $o$
     in the $i_j$-th query.
   \end{description}} *)
type var =
  | SRVar of II.rvar_id
  | ORVar of orvar_id * db_idx

 (* \ic{Formal sums use parameters in
     \begin{description}
     \item [OParam((m,o),j)] ${}=m^o_{i_j}$: parameter $m$ given to the oracle $o$ in the
       $i_j$-th query.
     \item [FieldChoice(w)] ${}=w$: parameter $w$ chosen by the adversary for the winning
       condition.
     \item [ICoeff(U,n)] ${}=\alpha^{(U,n)}$: Coefficient of $n$-th adversary input in
       $U \in \group$ chosen for winning condition.
     \item [OCoeff(U,o,n,j)] ${}=\beta_{i_j}^{(U,o,n)}$: Coefficient of $n$-th component of oracle output
       for $o$ in $i_j$-th call in $U \in \group$ chosen for winning condition.
     \item [CCoeff(U)] ${}=\gamma^{U}$: Constant in $U \in \group$ chosen for winning condition.
    \end{description}}*)
type param =
  | OParam      of oparam_id * db_idx
  | FieldChoice of II.fchoice_id
  | ICoeff      of II.gchoice_id * input_idx
  | OCoeff      of II.gchoice_id * II.oname * oreturn_idx * db_idx

(* \ic{A term consists of an integer and lists of
       (possibly indexed) parameters and random variables.
       We use terms to represent formal sums keeping $\Sigma$-binders implicit:
       \begin{itemize}
       \item $1,[w],[X]$ represents the product $w\,X$
       \item $[1],[\beta_{i_1}^{(U,o_1,3)}],[X;A^{o_1}_{i_1}]$ represents
          $\Sigma_{i_1 \in [q_{o_1}]}\, \beta_{i_1}^{(U,o_1,3)}\,X\,A^{o_1}_{i_1}$
       \item $[1], [\beta_{i_1}^{(U,o_1,3)}], [A^{o_1}_{i_1};\tilde{A}^{o_1}_{i_2}]$
          represents
          $\Sigma_{(i_2 \in [q_{o_1}])}
           \Sigma_{(i_1 \in [q_{o_1}] \setminus \{i_2\})}\,
             \beta_{i_1}^{(U,o_1,3)}\,A^{o_1}_{i_1}\,\tilde{A}^{o_1}_{i_2}$,
          i.e., for all index variables of random variables for the same oracle, we assume they range
          over distinct values. The missing values where $i_1=i_2$ are represented
          by $[1], [\beta_{i_1}^{(U,o_1,3)}], [A^{o_1}_{i_1};\tilde{A}^{o_1}_{i_1}]$.
          There are no implicit inequalities for index variables that only occur in parameters.
       \end{itemize}
       } *)
type term = IR.t * param list * var list

let term_compare (c1,ps1,vs1) (c2,ps2,vs2) =
  let cmp = IR.compare c1 c2 in
  if cmp <> 0 then cmp else compare (ps1,vs1) (ps2,vs2)

 (* \ic{A formal sum is a list of terms. We use formal sums as follows.
  \begin{enumerate}
  \item Represent group elements choosen by the adversary as linear combinations
    of adversary inputs and oracle return values. The resulting formal sums
    do not contain nested $\Sigma$'s.
  \item Products and sums of such formal sums. Multiplication can result in nested
     $\Sigma$'s and multiple index variables in terms.
  \item Transform formal sums over random variables and parameters into
    formal sums over random variables, i.e., coefficients are formal sums
    over parameters.
  \end{enumerate}
  Task 1. is trivial since we have at most one index variable per term.
  For Task 2., we have to (i) rename variables ensuring a unique representation for
  (indexed) monomials and
  (2) perform case distinctions on equalities to account for the implicit
  inequality conditions in our representation:\\
  $(\Sigma_{i_1} A_{i_1})*(\Sigma_{i_1} A_{i_1}) =
     \Sigma_{i_1} A^2_{i_1} + \Sigma_{i_1,i_2,i_1\neq i_2} A_{i_1} A_{i_2}$. }
*)
type t = term list

(*i*)
(*
let pp_var fmt v =
  match v with
  | SRVar(x)         -> F.fprintf fmt "%s" x
  | ORVar((a,on),i)  -> F.fprintf fmt "%s_(%s,i_%i)" a on i
*)

let pp_var fmt v =
  match v with
  | SRVar(x)        -> F.fprintf fmt "%s" x
  | ORVar((a,_o),i) -> F.fprintf fmt "%s_i%i" a i

(*
let pp_param fmt p =
  match p with
  | OParam((m,on),i) -> F.fprintf fmt "%s_(%s,i_%i)" m on i
  | FieldChoice(w)   -> F.fprintf fmt "%s" w
  | ICoeff(u,j)      -> F.fprintf fmt "a%%(%s,%i)" u j
  | OCoeff(u,o,j,i)  -> F.fprintf fmt "b%%(%s,%s,%i,i_%i)" u o j i
  | CCoeff(u)        -> F.fprintf fmt "c%%(%s)" u
*)

let pp_param fmt p =
  match p with
  | OParam((m,_o),i)  -> F.fprintf fmt "%s_i%i" m i
  | FieldChoice(w)    -> F.fprintf fmt "%s" w
  | ICoeff(u,j)       -> F.fprintf fmt "%s_I_%i" u j
  | OCoeff(u,_o,j,i)  -> F.fprintf fmt "%s_O_%i_i%i" u j i

let pp_monom fmt m = pp_list " * " pp_var fmt m

let pp_params fmt p = pp_list " * " pp_param fmt p

let pp_term fmt (c,p,m) =
  match p,m with
  | [], [] ->
    F.fprintf fmt "@[%a@]" IR.pp c
  | [], _ ->
    if IR.equal c IR.one
    then F.fprintf fmt "@[%a@]" pp_monom m
    else F.fprintf fmt "@[%a * %a@]" IR.pp c pp_monom m
  | _,[] ->
    if IR.equal c IR.one
    then F.fprintf fmt "@[%a@]" pp_params p
    else F.fprintf fmt "@[%a * %a@]" IR.pp c pp_params p
  | _ -> 
    if IR.equal c IR.one
    then F.fprintf fmt "@[%a * %a@]" pp_params p pp_monom m
    else F.fprintf fmt "@[%a * %a * %a@]" IR.pp c pp_params p pp_monom m

  
let pp_fsum fmt fs = F.fprintf fmt "@[%a@]" (pp_list " + " pp_term) fs
(*i*)

(*********************************************************************)
(* \hd{Formal sum: De Bruin indices} *)

(* \ic{Return De-Bruin-index for variable (if indexed).} *)
let db_idx_of_var = function ORVar((_,o),i) -> Some(i,o) | _ -> None

(* \ic{Return De-Bruin-index for parameter (if indexed).} *)
let db_idx_of_param p =
  match p with
  | OCoeff(_,o,_,i) | OParam((_,o),i) -> Some(i,o)
  | _ -> None

(* \ic{Return De-Bruin-indices occuring in term.} *)
let db_idx_of_term ps vs =
  (L.map db_idx_of_param ps @ L.map db_idx_of_var vs) |> catSome |> sorted_nub compare

(* \ic{Map the function [f] over all De-Bruin-indices in [v].} *)
let map_idx_var f v =
  match v with
  | ORVar(a,i) -> ORVar(a,f i)
  | _          -> v

(* \ic{Map the function [f] over all De-Bruin-indices in [p].} *)
let map_idx_param f p =
  match p with
  | OCoeff(u,o,j,i) -> OCoeff(u,o,j,f i)
  | OParam(m,i)     -> OParam(m,f i)
  | _               -> p

(* \ic{Shift De-Bruin-index in variable by offset.} *)
let shift_var offset = map_idx_var ((+) offset)

(* \ic{Shift De-Bruin-index in parameter by offset.} *)
let shift_param offset = map_idx_param ((+) offset)

(* \ic{Return the implicit inequalities between De Bruin indices as
       distinct-lists.} *)
let implicit_ineqs vs =
  db_idx_of_term [] vs
  |> L.sort (fun x y -> compare (snd x) (snd y))
  |> group (fun x y -> snd x = snd y)
  |> L.filter (fun l -> L.length l > 1)
  |> L.map (L.map fst)

(* \ic{Given a list of random variables containing De-Bruin-indices, return
       a canonical renaming of the De-Bruin-indices based on their occurences.
       Consider $\Sigma_{i_1,i_2} w_{i_1}\,A_{i_2}$ where the index $i_1$ only
       occurs in the parameter. Here, we only care about
       the index $i_2$ occuring in random variables for uniqueness. We therefore
       compute a canonical renaming for the indices occuring in random variables
       and later extend it to indices occuring in parameters arbitrarily.} *)
let canonical_renaming vs ps =
  let occ_v = function ORVar((x,o),i) -> Some(i,(x,o)) | _ -> None in
  let vidxs =
    catSome (L.map occ_v vs)
    |> L.sort (fun x y -> compare (fst x) (fst y))
    |> group  (fun x y -> fst x = fst y)
    |> L.map (fun g -> (fst (L.hd g), L.map snd g))
    |> L.map (fun (i,occs) -> (i, L.sort compare occs))
    |> L.sort (fun x y -> compare (snd x) (snd y))
    |> L.map fst
  in
  let pidxs =
    catSome (L.map db_idx_of_param ps)
    |> L.map fst
    |> L.filter (fun j -> not (L.mem j vidxs))
  in
  let c = ref 0 in
  L.map (fun j -> c := !c + 1; (j, !c - 1)) (vidxs@pidxs)

(* \ic{Return an inequality implied by the distinct lists [ineqs1] that
       is not implied by [ineqs2], if there is any.} *)
let missing_ineq ineqs1 ineqs2 =
  let rec expand_ineqs ieqs =
    match ieqs with
    | i::is ->
      conc_map (fun j -> if i = j then [] else [(i,j); (j,i)]) is @ expand_ineqs is
    | []    -> []
  in
  let ineqs1 = sii_of_list (conc_map expand_ineqs ineqs1) in
  let ineqs2 = sii_of_list (conc_map expand_ineqs ineqs2) in
  try  Some (Sii.choose (Sii.diff ineqs1 ineqs2))
  with Not_found -> None

(* \ic{Apply the substitution [sigma] of De-Bruin-indices to [v].} *)
let db_idx_subst_var sigma v =
    map_idx_var (fun i -> try L.assoc i sigma with Not_found -> i) v

(* \ic{Apply the substitution [sigma] of De-Bruin-indices to [p].} *)
let db_idx_subst_param sigma p =
  map_idx_param (fun i -> try L.assoc i sigma with Not_found -> i) p

(* \ic{Apply the substitution [sigma] of De-Bruin-indices to [ineqs].} *)
let db_idx_subst_ineqs sigma ineqs =
  L.map (L.map (fun i -> try L.assoc i sigma with Not_found -> i)) ineqs

(* \ic{Simplify the list of ineqs.} *)
let simp_ineqs ineqs =
  ineqs |> L.map (sorted_nub compare) |> L.filter (fun l -> L.length l > 1)

(* \ic{Create formal sum given a list of terms with at most one index variable.} *)
let of_terms ts =
  let ensure_one_ivar (_,ps,vs) =
    if L.length (db_idx_of_term ps vs) > 1
    then failwith "of_terms: term can contain at most one index variable"
  in
  L.iter ensure_one_ivar ts;
  L.sort term_compare (L.map (fun (c,ps,vs) -> (c, L.sort compare ps, L.sort compare vs)) ts)

let of_coeff c = [(c,[],[])]

let of_var v = [(IR.one,[],[v])]

let of_param p = [(IR.one,[p],[])]

(*********************************************************************)
(* \hd{Formal sum: addition and multiplication} *)

(* \ic{Addition is implemented by concatenating the lists of terms.
       We might want to simplify later on, but since we do not allow for
       sums of parameters as coefficients (e.g., $\beta\,X + \alpha\,X$
       is fine), something like $2\beta\,X + 3\beta\,X$ is fine too.
       We account for this in the function that computes the
       coefficient of $X$.} *)
let plus fs1 fs2 = fs1 @ fs2

let opp fs = L.map (fun (c,ps,vs) -> (IR.opp c,ps,vs)) fs

let const c = [(c,[],[])]

let one = [(IR.one,[],[])]

let zero = []

let param p = [(IR.one,[p],[])]

let var v = [(IR.one,[],[v])]

(* \ic{A raw term (i) contains explicit inequalities between De-Bruin-indices
       (using distinct-lists) and (ii) momonials might not be in normal-form.
       It is used for intermediate results to define multiplication.} *)
type raw_term = term * (db_idx list) list

let mult_raw_term (c1,ps1,vs1) (c2,ps2,vs2) : raw_term =
  let indices1 = db_idx_of_term ps1 vs1 |> L.map fst in
  let offset = from_opt ((+) 1) 0 (maximum indices1) in
  let ps2 = L.map (shift_param offset) ps2 in
  let vs2 = L.map (shift_var offset) vs2 in
  let ineqs1 = implicit_ineqs vs1 in
  let ineqs2 = implicit_ineqs vs2 in
  ( (IR.mult c1 c2, ps1 @ ps2, vs1 @ vs2)
  , ineqs1@ineqs2)

let rec terms_of_raw_term ((c,ps,vs),ineqs) =
  let imp_ineqs = implicit_ineqs vs in
  match missing_ineq imp_ineqs ineqs with
  | Some(i,j) ->
    let arg1 = ((c,ps,vs), [i;j]::ineqs) in
    let arg2 = ( (c
                 , L.map (db_idx_subst_param [(i,j)]) ps
                 , L.map (db_idx_subst_var   [(i,j)]) vs)
               , simp_ineqs (db_idx_subst_ineqs [(i,j)] ineqs))
    in
    terms_of_raw_term arg1 @ terms_of_raw_term arg2
  | None ->
    let sigma = canonical_renaming vs ps in
    let ps = L.sort compare (L.map (db_idx_subst_param sigma) ps) in
    let vs = L.sort compare (L.map (db_idx_subst_var sigma) vs) in
    [(c, ps, vs)]

let mult_fs_term fs t = conc_map (fun t' -> terms_of_raw_term (mult_raw_term t t')) fs

let mult fs1 fs2 = conc_map (fun t -> mult_fs_term fs2 t) fs1 |> L.sort term_compare

let ( *&) = mult

let ( +&) = plus

(*********************************************************************)
(* \hd{Formal sum: coefficients of random-variable-monomials} *)

(* \ic{Formal sum over parameters.} *)
type fs_param = (IR.t * param list) list

(* \ic{Formal sum over (indexed) random variables, i.e., coefficients are formal
       sums over parameters.
       We interpret $[ ( [ (1,\alpha_{i_1}\beta_{i_2}); (1,\gamma_{i_1}\beta_{i_2}) ], [A_{i_1}] )]$ as
       $\Sigma_{i_1} (\alpha_{i_1}*(\Sigma_{i_2} \beta_{i_2}) + \gamma_{i_1}*(\Sigma_{i_2} \beta_{i_2})) A_i$.
       As before, the inequalities are implicit for index variables occuring in the random
       variable monomials.
       For the representation, it should hold that the corresponding polynomial over the
       random variables is equal to $0$ iff all coefficients (formal sums over the
       parameters) are equal to $0$.} *)
type fs_rvars = (fs_param * var list) list

(* \ic{Return all momonials occuring in a formal sum. As before, 
       we interpret the returned monomial $A^{o_1}_{i_1} B^{o_1}_{i_2}$
       as $\forall i_1 \in [q_{o_1}], i_2 \in [q_{o_1}] \setminus \{i_1\}: A^{o_1}_{i_1} B^{o_1}_{i_2}$.} *)
let monoms fs = L.map (fun (_,_,vs) -> vs) fs |> sorted_nub compare

(* \ic{Return the coefficient (a formal sum over parameters) of [monom] in [fs].} *)
let coeff fs monom : fs_param =
  catSome (L.map (fun (c,ps,vs) -> if vs = monom then Some(c,ps) else None) fs)

(* \ic{Convert a formal sum (list of terms containing random variables and parameters)
       into a formal sum over random variables.} *)
let fs_to_fs_rvars fs : fs_rvars = L.map (fun vs -> (coeff fs vs, vs)) (monoms fs)

(* \ic{Constraints on parameters:
       The constraint \\
         $([(i_1,o_1);(i_2,o_1);(i_3,o_2)],
           [ (1,[\alpha_{i_1}; \alpha_{i_4}]);
             (1,[\alpha_{i_2}; \alpha_{i_3}]);
             (1,[\alpha_{i_2}; \alpha_{i_4}]) ]$
         represents \\
         $\forall i_1,i_2 \in [q_{o_1}], i_3 \in [q_{o_2}]:
           i_1 \neq i_2
           \Longrightarrow
           0 =   (\Sigma_{i_4} \alpha_{i_1}\,\alpha_{i_4})
               + \alpha_{i_2}\,\alpha_{i_3}
               + (\Sigma_{i_4} \alpha_{i_2}\,\alpha_{i_4})$.} *)
type param_constr = (db_idx * II.oname) list * fs_param

(* \ic{Convert a formal sum to constraints on parameters.} *)
let fs_to_constr fs =
  let fsr = fs_to_fs_rvars fs in
  L.map (fun (pfs,vs) -> (catSome (L.map db_idx_of_var vs), pfs)) fsr

(* \ic{Convert a formal sum to constraints on parameters for given set of bounds.} *)
let fs_to_bounded_constr _bounds _fs = failwith "undefined"

let compare_fsp fsp1 fsp2 =
  list_compare
    (fun (c1,ps1) (c2,ps2) ->
       let cmp = IR.compare c1 c2 in
       if cmp <> 0 then cmp
       else compare ps1 ps2)
    fsp1 fsp2

let compare_constr (binders1, fsp1) (binders2, fsp2) =
  let cmp = compare binders1 binders2 in
  if cmp <> 0 then cmp
  else compare_fsp fsp1 fsp2

let equal_fsp fsp1 fsp2 = compare_fsp fsp1 fsp2 = 0

let equal_constr constr1 constr2 = compare_constr constr1 constr2 = 0

(*i*)
let pp_fsp_term fmt (c,ps) =
  if IR.equal IR.one c
  then F.fprintf fmt "%a" pp_params ps
  else F.fprintf fmt "%a * %a" IR.pp c pp_params ps

let pp_fsp fmt fsp =
  match fsp with
  | [] -> F.fprintf fmt "0"
  | _  -> F.fprintf fmt "%a" (pp_list " + " pp_fsp_term) fsp

let pp_quant fmt (i,o) = F.fprintf fmt "i%i in [q_%s]" i o

let pp_binders fmt binders =
  match binders with
  | [] -> F.fprintf fmt ""
  | _  -> F.fprintf fmt "forall %a: " (pp_list ", " pp_quant) binders

let pp_param_constr rel fmt (binders,fsp) =
  let pos, neg = L.partition (fun (c,_) -> IR.compare c IR.zero > 0) fsp in
  let neg = L.map (fun (c,ps) -> (IR.opp c,ps)) neg in
  F.fprintf fmt "%a%a %s %a"  pp_binders binders pp_fsp pos rel pp_fsp neg

let pp_param_constr_ineq fmt (binders,fsp) =
  match binders with
  | [] ->
    F.fprintf fmt "%a <> 0" pp_fsp fsp
  | _ ->
    F.fprintf fmt "exists %a: %a <> 0" (pp_list ", " pp_quant) binders pp_fsp fsp

let pp_fsr_term fmt (fsp,rvs) =
  let binder =
    if L.exists (fun v -> db_idx_of_var v <> None) rvs
    then "Sum_{i0 in [q]} "
    else ""
  in
  match rvs with
  | [] -> 
    F.fprintf fmt "@[%s[%a]@]" binder pp_fsp fsp
  | _ -> 
    F.fprintf fmt "@[%s[%a](%a)@]" binder pp_fsp fsp (pp_list " * " pp_var) rvs

let pp_fs_rvars fmt fsr =
  F.fprintf fmt "@[%a@]" (pp_list "@.+ " pp_fsr_term) fsr

(*i*)
