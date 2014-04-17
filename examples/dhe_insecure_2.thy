setting symmetric.          (* symmetric (non-leveled) k-linear map *)
arity 3.                    (* fixes the arity k to 3 *)
problem_type decisional.

input
  [ 1
  , Y
  , forall i in [0,l - 1]: X^i
  , forall j in [0,l - 1]: X^(l + 1 + j) ] @ 1.

challenge Y*X^l @ 3.