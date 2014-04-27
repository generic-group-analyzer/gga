OCAMLBUILD=ocamlbuild
LIBFLAGS=
MENHIRFLAGS=-use-menhir -menhir "menhir -v"
FINDLIBFLAGS=-use-ocamlfind -classic-display
CFLAGS="-w +a-e-9"

INFRA_MODULES=Util/Util.ml Poly/PolyInterfaces.mli Poly/Poly.mli Poly/Poly.ml

NONPARAM_MODULES= NonParam/NonParamInput.mli NonParam/NonParamInput.ml \
  NonParam/NonParamCompletion.ml NonParam/NonParamCompletion.mli \
  NonParam/NonParamPredefined.ml \
  Solver/Sage_Solver.ml \
  NonParam/NonParamAnalyze.ml \
  NonParam/NonParamTest.ml

PARAM_MODULES=Param/ParamInput.mli Param/ParamInput.ml \
  Param/ParamConstraints.ml Solver/Z3_Solver.ml \
  Param/ParamParser.mly Param/ParamLexer.mll Param/ParamAnalyze.ml \
  Param/ParamTest.ml

TOOL_MODULES = Tool/ggt.ml

INFRA_FILES=$(addprefix src/,$(INFRA_MODULES))
NONPARAM_FILES=$(addprefix src/,$(NONPARAM_MODULES))
PARAM_FILES=$(addprefix src/,$(PARAM_MODULES))
TOOL_FILES=$(addprefix src/,$(TOOL_MODULES))


.PHONY: native doc paramtest

all: native

native:
	$(OCAMLBUILD) -tag annot -tag debug -cflags $(CFLAGS) $(LIBFLAGS) $(FINDLIBFLAGS) $(MENHIRFLAGS) src/Tool/ggt.native

byte:
	$(OCAMLBUILD) -tag annot -tag debug -cflags $(CFLAGS) $(LIBFLAGS) $(FINDLIBFLAGS) $(MENHIRFLAGS) src/Tool/ggt.byte
	OCAMLRUNPARAM="-b" ./ggt.byte examples/dhe.ggt

paramtest:
	$(OCAMLBUILD) -tag annot -tag debug -cflags $(CFLAGS) $(LIBFLAGS) $(FINDLIBFLAGS) $(MENHIRFLAGS) src/Param/ParamTest.native
	./ParamTest.native

nonparamtest:
	$(OCAMLBUILD) -tag annot -tag debug -cflags $(CFLAGS) $(LIBFLAGS) $(FINDLIBFLAGS) $(MENHIRFLAGS) src/NonParam/NonParamTest.native
	./NonParamTest.native

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