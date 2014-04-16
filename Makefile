OCAMLBUILD=ocamlbuild
LIBFLAGS=-lib unix 
MENHIRFLAGS=-use-menhir -menhir "menhir -v"
FINDLIBFLAGS=-use-ocamlfind -classic-display
CFLAGS="-w +a-e-9"

all: native

native:
	$(OCAMLBUILD) -tag annot -tag debug -cflags $(CFLAGS) $(LIBFLAGS) $(FINDLIBFLAGS) $(MENHIRFLAGS) src/Tool/ggt.native
	./ggt.native	