OCAMLBUILD=ocamlbuild
LIBFLAGS=
MENHIRFLAGS=-use-menhir -menhir "menhir -v"
FINDLIBFLAGS=-use-ocamlfind -classic-display
CFLAGS="-w +a-e-9"

INFRA_MODULES=Util/Util.ml Poly/PolyInterfaces.mli Poly/Poly.mli Poly/Poly.ml

NONPARAM_MODULES= NonParam/NonParamInput.mli NonParam/NonParamInput.ml \
  NonParam/NonParamCompletion.ml NonParam/NonParamCompletion.mli \
  Solver/Sage_Solver.ml \
  NonParam/NonParamParser.mly NonParam/NonParamLexer.mll \
  NonParam/NonParamAnalyze.ml \
  NonParam/NonParamTest.ml

PARAM_MODULES=Param/ParamInput.mli Param/ParamInput.ml \
  Param/ParamConstraints.ml Solver/Z3_Solver.ml \
  Param/ParamParser.mly Param/ParamLexer.mll Param/ParamAnalyze.ml \
  Param/ParamTest.ml

INTERACTIVE_MODULES=Interactive/InteractiveInput.ml \
  Interactive/InteractiveParser.mly \
  Interactive/InteractiveLexer.mll \
  Interactive/InteractiveBounded.ml \
  Interactive/InteractiveFormalSum.ml \
  Interactive/InteractiveUnbounded.ml \
  Interactive/InteractiveAnalyze.ml \
  Interactive/InteractiveTest.ml

TOOL_MODULES = Tool/ggt.ml

INFRA_FILES=$(addprefix src/,$(INFRA_MODULES))
NONPARAM_FILES=$(addprefix src/,$(NONPARAM_MODULES))
PARAM_FILES=$(addprefix src/,$(PARAM_MODULES))
INTERACTIVE_FILES=$(addprefix src/,$(INTERACTIVE_MODULES))
TOOL_FILES=$(addprefix src/,$(TOOL_MODULES))


.PHONY: native doc paramtest

all: native wsggt

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

interactivetest:
	$(OCAMLBUILD) -tag annot -tag debug -cflags $(CFLAGS) $(LIBFLAGS) $(FINDLIBFLAGS) $(MENHIRFLAGS) src/Interactive/InteractiveTest.native
	./InteractiveTest.native

wsggt:
	$(OCAMLBUILD) -tag annot -tag debug -cflags $(CFLAGS) $(LIBFLAGS) $(FINDLIBFLAGS) $(MENHIRFLAGS) src/Tool/wsggt.native

webdoc:
	pandoc -s -S --toc -c buttondown.css web/help.md > web/help.html

clean:
	$(OCAMLBUILD) -clean

loc:
	find src -name \*.ml\* | xargs wc -l

doc:
	ocamlweb doc/prelude.tex \
	  doc/chap-infra.tex $(INFRA_FILES) \
	  doc/chap-nonparam.tex $(NONPARAM_FILES) \
	  doc/chap-param.tex $(PARAM_FILES) \
	  doc/chap-interactive.tex $(INTERACTIVE_FILES) \
	  doc/chap-tool.tex $(TOOL_FILES) \
	  doc/close.tex --no-preamble --header > doc/tool.tex
	echo "\end{document}" >> doc/tool.tex
	cd doc && latexmk -pdf tool.tex
