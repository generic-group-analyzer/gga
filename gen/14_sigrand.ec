map G1 * G2 -> GT.
iso G2 -> G1.
input [V,W] in G1.
input [ sR, sM, V + W + W*sM + sM*sR + sR*sR ] in G2.
oracle o1(M:G2) =
  sample R;
  return [ R, V + W + M*W + M*R + R*R ] in G2.

win (wM:G2, wR:G2, wS:G2) = (wM <> M /\ wM <> sM /\ 0 = V + W + wM*W + wM*wR + wR*wR - wS).