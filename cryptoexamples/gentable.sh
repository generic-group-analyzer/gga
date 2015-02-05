#/bin/bash

echo "=========================="
echo "Non-Parametric Assumptions"
echo "=========================="
echo
echo "=== DBDH ==="
time ./ggt.native nonparam cryptoexamples/nonparametric/DBDH.ggt | tail -1
echo
echo "=== Freeman 3 ==="
time ./ggt.native nonparam cryptoexamples/nonparametric/Freeman-3.ggt | tail -1
echo
echo "=== Freeman 4 ==="
time ./ggt.native nonparam cryptoexamples/nonparametric/Freeman-4.ggt | tail -1
echo
echo "=== k-lin, k=1,...,4 ==="
time ./ggt.native nonparam cryptoexamples/nonparametric/1-lin.ggt | tail -1
time ./ggt.native nonparam cryptoexamples/nonparametric/2-lin.ggt | tail -1
time ./ggt.native nonparam cryptoexamples/nonparametric/3-lin.ggt | tail -1
time ./ggt.native nonparam cryptoexamples/nonparametric/4-lin.ggt | tail -1
echo
echo "=== 2-lin with 3-linear map ==="
time ./ggt.native nonparam cryptoexamples/nonparametric/2-lin-3-linmap.ggt | tail -1
echo
echo "=== 2-SCasc ==="
time ./ggt.native nonparam cryptoexamples/nonparametric/2-SCasc.ggt | tail -1
echo
echo "=== 2-BDH ==="
time ./ggt.native nonparam cryptoexamples/nonparametric/2-BDH.ggt | tail -1
echo
echo "======================"
echo "Parametric Assumptions"
echo "======================"
echo
echo "=== l-DHE ==="
time ./ggt.native param cryptoexamples/parametric/DHE.ggt | tail -1
echo
echo "=== l-DHI ==="
time ./ggt.native param cryptoexamples/parametric/DHI.ggt | tail -1
echo
echo "=== (l,k)-MMDHE ==="
time ./ggt.native param cryptoexamples/parametric/mmdhe_simplified.ggt | tail -1
echo
echo "======================"
echo "Generalized Extraction"
echo "======================"
echo
echo "=== 5-SDH ==="
time ./ggt.native interactive_0 cryptoexamples/interactive/5-SDH.ggt | tail -1
echo
echo "======================="
echo "Interactive Assumptions"
echo "======================="
echo
echo "=== LRSW (q=4) ==="
time ./ggt.native interactive_4 cryptoexamples/interactive/LRSW.ggt | tail -1
echo
echo "=== m-LRSW (q=2) ==="
time ./ggt.native interactive_2 cryptoexamples/interactive/m-LRSW.ggt | tail -1
echo
echo "=== IBSAS (q=3) ==="
time ./ggt.native interactive_3 cryptoexamples/interactive/IBSAS.ggt | tail -1
echo
echo "=== Strong-LRSW (q=4) ==="
time ./ggt.native interactive_4 cryptoexamples/interactive/strong-LRSW.ggt | tail -1
echo
echo "=== s-LRSW (q=4) ==="
time ./ggt.native interactive_4 cryptoexamples/interactive/s-LRSW.ggt | tail -1
echo
echo "==========================="
echo "Composite-Order Assumptions"
echo "==========================="
echo
echo "=== KSW, Assumption 1 ==="
time ./ggt.native nonparam cryptoexamples/composite/KSW1.ggt | tail -1
