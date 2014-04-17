open Parametric_Input
open Ggt
open Util

module F = Format

(*******************************************************************)
(* Tests *)

let l_dhe =
  { setting      = Some Symmetric;
    problem_type = Some Decisional;
    arity        = Some(2);
    challenge    = Some (p_challenge "challenge Y*X^(l + 1) @ 2.");
    inputs       = p_input_line
"input \
  [ 1\
  , Y\
  , forall i in [0,l - 1]: X^i\
  , forall j in [0,l + 1]: X^(l + 1 + j) ] @ 1."
  }

let l_dhe_wrong =
  { setting      = Some Symmetric;
    problem_type = Some Decisional;
    arity        = Some(2);
    challenge    = Some(p_challenge "challenge Y*X^(l + 1) @ 2.");
    inputs       = p_input_line
"input \
  [ 1\
  , Y\
  , forall i in [0,l - 1]: X^i\
  , forall j in [0,l + 1]: X^(l + 1 + j) ] @ 1."
  }

let l_dhi =
  { setting      = Some Symmetric;
    problem_type = Some Decisional;
    arity        = Some(1);
    challenge    = Some(p_challenge "challenge X^((2 * l) + 1) @ 2.");
    inputs       = p_input_line
"input \
  [ 1\
  , forall i in [0,l]: X^i ] @ 1,\
  [ 1 ] @ 2."
  }


let stheory = "\
setting symmetric.  (* symmetric (non-leveled) k-linear map *)\
arity 2.            (* fixes the arity k to 2 *)\
problem_type decisional. (* we handle decisional and computational problems *)\
\
input \
  [ 1\
  , Y\
  , forall i in [0,l - 1]: X^i\
  , forall j in [0,l + 1]: X^(l + 1 + j) ] @ 1.\
challenge Y*X^(l + 1) @ 2."

let () =
  (* analyze l_dhe; *)
  (* analyze l_dhe_wrong; *)
  (* analyze l_dhi; *)
  let cmds = p_cmds stheory in
  F.printf "\n\n%a" (pp_list "@\n" pp_cmd) cmds;
  let assm = eval_cmds cmds in
  F.printf "\n\n%a" pp_assumption assm;
  analyze assm


