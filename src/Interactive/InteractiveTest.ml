(*s Tests for interactive assumptions *)

(*i*)

module IA = InteractiveAnalyze
module FS = InteractiveFormalSum
(*i*)

let def_lrsw =
  "input [X, Y] in G.\n"^
  "oracle o1(m:Fp) = A <-$ G; return (A, Y*A, X*A + m*X*Y*A)."^
  "win (U:G, V:G, W:G, m':Fp) = ( V - U*Y = 0 /\\ W - U*X - m'*U*X*Y = 0 /\\ U <> 0 /\\ m <> m')."

let def_strong_lrsw =
  "input [S, T] in G.\n"^
  "oracle o1(x:Fp) = A <-$ G; return (A, A*T, A*S + x*A*S*T, x*A*T)."^
  "win (A1:G, A2:G, A3:G, A4:G, A5:G,x':Fp) = ( A2 - A1*T = 0 /\\ A3 - A1*S - x'*A1*S*T = 0 /\\ A4 - x'*A1 = 0 /\\ A5 - x'*A1*T = 0\
    /\\ x <> x' /\\ A1 <> 0)."

let def_slrsw =
  "input [X, Y] in G.\n"^
  "oracle o1(m:Fp) = A <-$ G; return (A, A*X + m*A*Y)."^
  "win (U:G,V:G,m':Fp) = ( V - U*X - m'*U*Y = 0 /\\ m <> m' /\\ U <> 0)."


(*i*)

(*
let () =
  IA.analyze_from_string def_slrsw
*)

(*i*)