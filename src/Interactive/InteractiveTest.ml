(*s Tests for interactive assumptions *)

(*i*)
open InteractiveInput
open InteractiveAnalyze
open Util
(*i*)

(*******************************************************************)
(* \hd{LRSW example} *)

(* \ic{The adversary obtains $X$ and $Y$ as initial input.} *)
let inputs = [ RP.var "X"; RP.var "Y" ]

(* \ic{The adversary can query the oracle with $m$ and obtains
       $(A, A\,Y, A\,X + m\,A\,X\,Y)$ for a freshly sampled~$X$.} *)
let oracle =
  let vA    = OP.var (ORVar "A") in
  let vX    = OP.var (SRVar "X") in
  let vY    = OP.var (SRVar "Y") in
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
  let vV    = WP.var (GroupChoice "V") in
  let vW    = WP.var (GroupChoice "W") in
  let vm'   = WP.var (FieldChoice "m'") in
  let vm    = WP.var (OParam "m") in
  let (+)   = WP.add in
  let ( * ) = WP.mult in  
  let (-)   = WP.minus in
  {
    wcond_ineqs = [ vU; vm' - vm ];
    wcond_eqs   = [ vV - vU*vX; vW - vU*vX + vm'*vU*vX*vY ];
  }

let gd =
  {
    gdef_inputs = inputs;
    gdef_odefs  = [ ("o", oracle) ];
    gdef_wcond  = wcond;
  }

let def_string =
  "input [X, Y] in G.\n"^
  "oracle o1(m:Fp) = A <-$ G; return (A, Y*A, X*A + m*X*Y*A)."^
  "oracle o2(w:Fp) = E <-$ G; return (E, Y*E, X*E + w*X*Y*E)."^
  "win (U:G, V:G, W:G, m':Fp) = ( V - U*X = 0 /\\ W - U*X + m'*U*X*Y = 0 /\\ U <> 0 /\\ m' - m <> 0 )."

(*i*)
let tpp () =
  F.printf "%a\n\n" pp_gdef gd

let () =
  let gdef = p_cmds def_string |> eval_cmds in
  F.printf "%a\n\n" pp_gdef gdef
(*i*)