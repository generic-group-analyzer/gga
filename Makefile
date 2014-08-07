OCAMLBUILD=ocamlbuild
LIBFLAGS=-lflags -cclib,-lpari -cflags -ccopt,-I/usr/local/include/pari -lflags -cclib,-force_load,c_src/libparistubs.a
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
  Interactive/InteractiveEval.ml \
  Interactive/InteractiveParser.mly \
  Interactive/InteractiveLexer.mll \
  Interactive/InteractiveBounded.ml \
  Interactive/InteractiveFormalSum.ml \
#  Interactive/InteractiveUnbounded.ml \
  Interactive/InteractiveAnalyze.ml \
  Interactive/InteractiveTest.ml

SYNTH_MODULES=Synthesis/Synthesis.ml

TOOL_MODULES = Tool/ggt.ml

INFRA_FILES=$(addprefix src/,$(INFRA_MODULES))
NONPARAM_FILES=$(addprefix src/,$(NONPARAM_MODULES))
PARAM_FILES=$(addprefix src/,$(PARAM_MODULES))
INTERACTIVE_FILES=$(addprefix src/,$(INTERACTIVE_MODULES))
SYNTH_FILES=$(addprefix src/,$(SYNTH_MODULES))
TOOL_FILES=$(addprefix src/,$(TOOL_MODULES))


.PHONY: native doc paramtest

all: native # wsggt

native:
	test -d _build/c_src || mkdir -p _build/c_src
	gcc -c c_src/pari_stubs.c -o _build/c_src/pari_stubs.o
	ar rc _build/c_src/libparistubs.a _build/c_src/pari_stubs.o
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
	pandoc -s -S --toc -c buttondown.css README > web/help.html

clean:
	-rm doc/tool.pdf
	$(OCAMLBUILD) -clean

loc:
	find src -name \*.ml\* | xargs wc -l

doc:
	ocamlweb doc/prelude.tex \
	  doc/chap-infra.tex $(INFRA_FILES) \
	  doc/chap-nonparam.tex $(NONPARAM_FILES) \
	  doc/chap-param.tex $(PARAM_FILES) \
	  doc/chap-interactive.tex $(INTERACTIVE_FILES) \
	  doc/chap-synth.tex $(SYNTH_FILES) \
	  doc/chap-tool.tex $(TOOL_FILES) \
	  doc/close.tex --no-preamble --header > doc/tool.tex.tmp
	echo "\end{document}" >> doc/tool.tex.tmp
	mv doc/tool.tex.tmp doc/tool.tex
	cd doc && latexmk -pv -pdf tool.tex

%.inferred.mli:
	ocamlbuild -use-ocamlfind $(OCAMLBUILDFLAGS) src/$@ && cat _build/src/$@
