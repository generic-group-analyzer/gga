OCAMLBUILD=ocamlbuild
LIBFLAGS=-lib unix 
MENHIRFLAGS=-use-menhir -menhir "menhir -v"
FINDLIBFLAGS=-use-ocamlfind -classic-display
CFLAGS="-w +a-e-9"

INFRA_MODULES=Util/Util.ml Poly/PolyInterfaces.mli Poly/Poly.mli Poly/Poly.ml

NONPARAM_MODULES= NonParam/NonParamInput.ml

PARAM_MODULES=Parametric/ParametricInput.mli Parametric/ParametricInput.ml \
  Parametric/ParametricConstraints.ml Solver/Z3_Solver.ml \
  Parser/Parser.mly Parser/Lexer.mll Parametric/ParametricAnalyze.ml

TOOL_MODULES = Tool/ggt.ml

INFRA_FILES=$(addprefix src/,$(INFRA_MODULES))
NONPARAM_FILES=$(addprefix src/,$(NONPARAM_MODULES))
PARAM_FILES=$(addprefix src/,$(PARAM_MODULES))
TOOL_FILES=$(addprefix src/,$(TOOL_MODULES))


.PHONY: native doc paramtest

all: native

native:
	$(OCAMLBUILD) -tag annot -tag debug -cflags $(CFLAGS) $(LIBFLAGS) $(FINDLIBFLAGS) $(MENHIRFLAGS) src/Tool/ggt.native
	./ggt.native examples/dhe.thy

paramtest:
	$(OCAMLBUILD) -tag annot -tag debug -cflags $(CFLAGS) $(LIBFLAGS) $(FINDLIBFLAGS) $(MENHIRFLAGS) src/Tool/Param_test.native
	./Param_test.native

clean:
	$(OCAMLBUILD) -clean

doc:
	ocamlweb doc/prelude.tex \
	  doc/chap-infra.tex $(INFRA_FILES) \
	  doc/chap-nonparam.tex $(NONPARAM_FILES) \
	  doc/chap-param.tex $(PARAM_FILES) \
	  doc/chap-tool.tex $(TOOL_FILES) \
	  doc/close.tex --no-preamble --header > doc/tool.tex
	echo "\end{document}" >> doc/tool.tex
	cd doc && latexmk -pdf tool.tex