setting symmetric.          (* symmetric (non-leveled) k-linear map *)
arity 2.                    (* fixes the arity k to 3 *)
problem_type decisional.

input
  [ 1
  , forall i in [0,l]: X^i ] @ 1.

challenge X^(2*l + 1) @ 2.