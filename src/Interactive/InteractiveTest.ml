(*s Tests for interactive assumptions *)

(*i*)
open InteractiveInput
(*i*)

(*******************************************************************)
(* \hd{LRSW example} *)

(* \ic{The adversary obtains $X$ and $Y$ as initial input.} *)
let inputs = [ RP.var "X"; RP.var "Y" ]

(* \ic{The adversary can query the oracle with $m$ and obtains
       $(A, A\,Y, A\,X + m\,A\,X\,Y)$ for a freshly sampled~$X$.} *)
let oracle =
  let vA    = OP.var (FRVar "A") in
  let vX    = OP.var (GRVar "X") in
  let vY    = OP.var (GRVar "Y") in
  let vm    = OP.var (Param "m") in
  let (+)   = OP.add in
  let ( * ) = OP.mult in
  [ vA; vA * vY; vA * vX + vm * vA * vX * vY ]

(* \ic{The adversary must choose $U,V,W \in \group$ and
       $m' \in \field$ such that 
       $U \neq 0$, $\forall i \in [q].\, m' \neq m_i$,
       $V = U\,X$, and $W = U\,X + m'\,U\,X\,Y$.} *)
let wcond =
  let vX    = WP.var (RVar "X") in
  let vY    = WP.var (RVar "Y") in
  let vU    = WP.var (GroupChoice "U") in
  let vV    = WP.var (GroupChoice "U") in
  let vW    = WP.var (GroupChoice "W") in
  let vm'   = WP.var (FieldChoice "m'") in
  let vm    = WP.var (OArg "m") in
  let (+)   = WP.add in
  let ( * ) = WP.mult in  
  let (-)   = WP.minus in
  {
    wcond_ineqs = [ vU; vm' - vm ];
    wcond_eqs   = [ vV - vU*vX; vW - vU*vX + vm'*vU*vX*vY ];
  }

let () =
  f ()