open Util
open Parametric_Input
open Parametric_Constr


module F = Format


(*******************************************************************)
(* Tests *)

let mk_re qp f = (LevelFixed 1, mk_rexpr qp f)
let forall c l d f = mk_re [(c,l,d)] f
let l1   = ExpPoly.var (Rlimit 1)
let r1   = ExpPoly.var (Ridx 1)
let c i  = ExpPoly.const i
let (+)  = ExpPoly.add
let (^) s f = [(s,f)]
let one = ExpPoly.one

let bdhe =
  let input = 
    [ (* M1 = 1 *)
      mk_re [] []
      (* M2 = Y *)
    ; mk_re [] [("Y",one)] 
      (* M3 = All r1 in [0,l1]. X^r1 *)
    ; forall 0 1 0 ("X"^r1)
      (* M4 = All r1 in [0,l1]. X^(l1 + 1 + r1 *)
    ; forall 0 1 0 ("X" ^ (l1 + (c 2) + r1))
    ]
  in
  let challenge = (LevelFixed 2, ("Y"^(c 1))) in
  (input,challenge)

let test (input,challenge) =
  let constrs = gen_constrs input challenge in
  F.printf "input: @\n  %a@\n@\n"
    (pp_list "@\n  " (fun fmt (i,re) -> Format.fprintf fmt "%i: %a" i pp_rexpr_level re))
    (mapi' (fun i inp -> (i,inp)) input);
  F.printf "challenge: %a @@ level %a\n\n" pp_input_monomial (snd challenge) pp_level (fst challenge);
  F.printf "constrs:\n  %a\n" (pp_list "\n  " pp_constr) constrs;
  print_newline ();
  Z3_Solver.solve constrs

let () = test bdhe
