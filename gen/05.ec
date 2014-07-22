map G1 * G2 -> GT.
iso G2 -> G1.
input [V,W] in G1.
oracle o1(M:G2) =
  sample R;
  return [ R, V + M*R^-1 + W*R^-1 + M*W*R^-1 ] in G2.

win (wM:G2, wR:G2, wS:G2) = (wM <> M /\ 0 = wM + W + wM*W + V*wR - wR*wS).
