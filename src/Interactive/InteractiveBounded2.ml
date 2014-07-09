(* Query index: 1,..,q *)
type query_idx = int

(* Coefficient index: the j-th coefficient in linear combination of terms *)
type coeff_idx = int

(* \begin{itemize}
   \item for sampled shared variables: $V,W$
   \item for variables sampled in oracles: $R_1,..,R_q$
   \end{itemize}
*)
type rvar =
  | SRVar of id
  | ORVar of id * query_idx

(* \begin{itemize}
   \item $m$ in LRSW
   \item $\alpha^{M}_{i,j}$: coefficient of $j$-th element in the completion
      (for the right group) before calling the oracle the $i$-time.
  \item $mm$ in LRSW
  \item $\beta^{M'}_j$: coefficient of $j$-th element in the completion
      after performing the last oracle call.
  \end{itemize}
*)
type param =
  | FOParam of id * query_idx
  | OCoeff  of id * query_idx * coeff_idx
  | FChoice of id
  | ChoiceCoeff of id * coeff_idx

(* Variables for $\ZZ[RVars,Params]$ *)
type var =
  | RVar of rvar
  | Param of param

(* define \ZZ[RVars,Params] *)

(* define \ZZ[Params] *)

(* define (\ZZ[Params])[RVars] for coefficient extraction/pretty printing. *)

(* 1. conversion from rpoly given as adversary input to \ZZ[RVars,Params] *)

(* 2. conversion from opoly + completion + query_index to \ZZ[RVars,Params] *)

(* 3. conversion from wpoly + completion to \ZZ[RVars,Params] *)

(* 4. completion computation *)

(* 5. Sending everything to Sage *)
