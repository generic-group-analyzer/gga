setting symmetric.          (* symmetric (non-leveled) k-linear map *)
arity 2.                    (* fixes the arity k to 2 *)
problem_type decisional.

input
  [ 1
  , Y
  , forall i in [0, l - 1]: X^i
  , forall j in [l + 1, 2*l]: X^j ] @ 1.

challenge Y*X^l @ 2.