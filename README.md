# Generic Group Analyzer

## Installation

Use 'make' to compile the commandline tool 'ggt.native'.

Then run 'make install' to install the binary files in your system.

You need an up-to-date ocaml installation with the packages
'menhir', 'yojson', and 'ounit'.

Usually, the easiest way to achieve this is by using opam [^opam]. Our tool
uses Sage, Pari/GP, and Z3 as a backend.

For Sage[^Sage], you should be able to start 'sage -python'. For Pari/GP
[^Pari], you need to be able to compile and link C code with libpari.
On OS X, you can install Pari/GP with homebrew and on Ubuntu, the package
is named libpari-dev. We use a Z3 wrapper written in Python. This requires the Z3
Python bindings [^Z3Py] to work. You can test the interaction of our tool with
Sage and Z3 by running './scripts/ggt_Sage.py test' and './scripts/ggt_z3.py test'.

[^opam]: [http://opam.ocaml.org/doc/Quick_Install.html](http://opam.ocaml.org/doc/Quick_Install.html)
[^Sage]: [http://www.sagemath.org](http://www.sagemath.org)
[^Pari]: [http://pari.math.u-bordeaux.fr/](http://pari.math.u-bordeaux.fr/)
[^Z3Py]: [http://z3.codeplex.com](http://z3.codeplex.com) (you might have to set PYTHONPATH)

## Batch mode

You can use the batch mode by running, e.g.:

~~~~~
$ generic-group-analyzer nonparam tests/nonparam/valid/ddh_bilin_asym.ggt
~~~~~

The tool supports four modes given as first argument:
- nonparam: for analyzing non-parametric assumptions
- param: for analyzing parametric assumptions
- interactive_i (for i in 1,2,3,..): for analyzing interactive assumptions
    with the given bound i on oracle queries
- interactive: for analyzing interactive assumptions without giving
    a bound on the number of queries

These different modes differ in the support for group settings and problem
descriptions. For the interactive mode, unbounded verification supports
a strict subset of the problems supported by bounded verification.

### Non-parametric

We use DDH in an asymmetric group with a pairing as an example:

~~~~~
(* DDH in G2 of asymmetric bilinear group *)

isos G1 -> G2.

maps G1 * G2 -> GT.

input [ X, Y ] in G2.

input_left [ X*Y ] in GT.

input_right [ Z ] in GT.
~~~~~

We use ``(*`` and ``*)`` as comment markers, ``G*`` for group names,
and uppercase identifiers for random variables. The adversary input is
given as a polynomial "in the exponent". Here, we specify the group
setting by giving the isomorphisms and bilinear maps first.
Then we give the common input and afterwards the left and right
input.

See [tests/nonparam/](tests/nonparam/) for more examples.

#### Composite-order assumptions

We also support non-parametric composite-order assumptions.
See [tests/nonparam/valid/subgroup_1.ggt](tests/nonparam/valid/subgroup_1.ggt)
for an example. We use tuples of polynomials to define the exponents
of the generators of the subgroups.

### Parametric

We use DHE as an example.

~~~
setting symmetric.           (* symmetric (leveled) multilinear map *)
levels 2.                    (* fixes the number of levels to 2 *)
problem_type decisional.

input
  [ 1
  , Y
  , forall i in [0, l - 1]: X^i
  , forall j in [l + 1, 2*l]: X^j ] @ 1.

challenge Y*X^l @ 2.
~~~

Since we only support computational or real-or-random problems, the problem
is always specified by giving the input and the challenge. Depending on
the ``problem_type``, the adversary must either compute the challenge
or distinguish it from a random value.

We can analyze the assumption using

~~~~~
$ generic-group-analyzer param tests/param/valid/ddhe.ggt
~~~~~


See [tests/param/](tests/param/) for more examples.

### Interactive bounded

We use the mLRSW problem as an example.

~~~~~
input [1, A, B, U, V] in G.

oracle o1(m:Fp) = R <-$ G; return (m*U*R + A*B, V*R + A*B, R).

win (X:G, S1:G, S2:G, mm:Fp) =
  ( S1 = mm*U*X + A*B /\ S2 = V*X + A*B
    /\ m <> mm /\ X <> 0 /\ m <> 0 /\ mm <> 0).
~~~~~

We support problems where the adversary ouput is located in the
source group ``G''. In this case, the group structure does not help
the adversary to win the (computational) experiment.

An interactive experiment consists of the adversary input,
the oracle definition, and a winning condition.

We can analyze the assumption using

~~~~~
$ generic-group-analyzer interactive_2 tests/interactive/attack/mLRSW_bounded.ggt
~~~~~

See [tests/interactive/](tests/interactive/) for more examples.

### Interactive unbounded
[Interactive unbounded is currently broken]

We use the LRSW problem as an example.

~~~~~
input [1,X, Y] in G.

oracle o1(m:Fp) = A <-$ G; return (A, Y*A, X*A + m*X*Y*A).

win (U:G, V:G, W:G, mm:Fp) =
  ( V - U*Y = 0 /\ W - U*X - mm*U*X*Y = 0 /\ U <> 0 /\ m <> mm /\ mm <> 0 /\ m <> 0).
~~~~~

We can analyze the assumption using

~~~~~
$ generic-group-analyzer interactive tests/interactive/valid/LRSW_unbounded.ggt
~~~~~

See [tests/interactive/](tests/interactive/) for more examples.

### Additional Problem Types

We have applied variants of our algorithm to the
interactive decisional problems CDDH1/CDDH2 presented
in [^IDDH]. The corresponding algorithm is not integrated
into the tool and a separate implementation is given in
scripts/interactive_decisional.

[^IDDH]: [www.di.ens.fr/~mabdalla/papers/AbPo05b-letter.pdf](www.di.ens.fr/~mabdalla/papers/AbPo05b-letter.pdf)