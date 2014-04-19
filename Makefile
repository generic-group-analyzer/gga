OCAMLBUILD=ocamlbuild
LIBFLAGS=-lib unix 
MENHIRFLAGS=-use-menhir -menhir "menhir -v"
FINDLIBFLAGS=-use-ocamlfind -classic-display
CFLAGS="-w +a-e-9"

MODULES=Util/Util.ml Poly/Poly.ml Poly/Poly.mli Parametric/ParametricInput.ml \
  Parametric/ParametricConstraints.ml Solver/Z3_Solver.ml \
  Parser/Parser.mly Parser/Lexer.mll Tool/ggt.ml

FILES=$(addprefix src/,$(MODULES))

.PHONY: native doc paramtest

all: native doc

native:
	$(OCAMLBUILD) -tag annot -tag debug -cflags $(CFLAGS) $(LIBFLAGS) $(FINDLIBFLAGS) $(MENHIRFLAGS) src/Tool/ggt.native
	./ggt.native examples/dhe.thy

paramtest:
	$(OCAMLBUILD) -tag annot -tag debug -cflags $(CFLAGS) $(LIBFLAGS) $(FINDLIBFLAGS) $(MENHIRFLAGS) src/Tool/Param_test.native
	./Param_test.native

clean:
	$(OCAMLBUILD) -clean

doc:
	ocamlweb doc/prelude.tex $(FILES) doc/close.tex --latex-option "novisiblespaces" \
	  --header -p "\usepackage{hyperref,framed,amsmath,amsfonts,amsthm}" > doc/tool.tex
	# cd doc && latexmk -pdf tool.tex