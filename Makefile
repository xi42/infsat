#SOURCE = flags.ml utilities.ml setqueue.ml obdd.mli obdd.ml pobdd.mli pobdd.ml syntax.ml parser.mli parser.ml lexer.ml grammar.ml automaton.ml alternatingAutomaton.mli alternatingAutomaton.ml conversion.ml stype.ml ai.ml type.ml cegen.ml saturate.ml main.ml
SOURCE = flags.ml profiling.ml utilities.ml setqueue.ml syntax.ml infSatParser.mli infSatParser.ml infSatLexer.ml grammar.ml conversion.ml stype.ml cfa.ml type.ml saturate.ml main.ml

all: infsat-debug TAGS

infSatParser.mli parser.ml: infSatParser.mly
	ocamlyacc infSatParser.mly
infSatLexer.ml: infSatLexer.mll
	ocamllex infSatLexer.mll

infsat: $(SOURCE)
# -unsafe can be considered
	ocamlopt -inline 1000 -o infsat unix.cmxa $(SOURCE)

top: $(SOURCE)
	ocamlmktop -o top unix.cma $(SOURCE)

infsat-debug: $(SOURCE)
	ocamlc -g -o infsat-debug unix.cma $(SOURCE)

.SUFFIXES:
	.ml .cmo .mli .cmi

.PHONY:
	all clean

TAGS: $(SOURCE)
	ctags -e $(SOURCE)

doc: $(SOURCE)
	ocamldoc -html -d doc $(SOURCE)

clean:
	rm -f *.cmi *.cmx *.o *.cmo *.exe infsat top infSatParser.ml infSatParser.mli infSatLexer.ml TAGS infsat-debug
