SOURCE_PRE = flags.ml utilities.ml timing.ml sortedList.ml setQueue.ml twoLayerQueue.ml batchQueue.ml syntax.ml
SOURCE_GEN = infSatParser.mli infSatParser.ml infSatLexer.ml
SOURCE_POST = grammarCommon.ml grammar.ml conversion.ml etaExpansion.ml hGrammar.ml binding.ml cfa.ml type.ml typingCommon.ml proof.ml htyStore.ml environment.ml targetEnvms.ml typing.ml duplicationFactorGraph.ml saturation.ml main.ml
SOURCE = $(SOURCE_PRE) $(SOURCE_GEN) $(SOURCE_POST)

all: infsat parencol

install-dependencies:
	opam install oUnit utop

infSatParser.mli infSatParser.ml: infSatParser.mly
	ocamlyacc infSatParser.mly

infSatLexer.ml: infSatLexer.mll
	ocamllex infSatLexer.mll

infsat: $(SOURCE) main_wrapper.ml
# consider -unsafe
	ocamlopt -inline 999 -o $@ str.cmxa $^

infsat-g: $(SOURCE) main_wrapper.ml
	ocamlopt -g -o $@ str.cmxa $^

infsat-prof-debug: $(SOURCE) main_wrapper.ml
	ocamlcp -c $(SOURCE_PRE)
	ocamlc -c $(SOURCE_GEN)
	ocamlcp -c $(SOURCE_POST) main_wrapper.ml
	ocamlcp -o $@ str.cma $(filter %.cmo,$(SOURCE:.ml=.cmo)) main_wrapper.cmo

top: $(SOURCE) test.ml utop_wrapper.ml
	ocamlfind ocamlc -o $@ -thread -linkpkg -linkall -predicates create_toploop -package compiler-libs.toplevel,oUnit,utop -g str.cma $^

infsat-debug: $(SOURCE) main_wrapper.ml
	ocamlfind ocamlc -o $@ -g str.cma $^

test: $(SOURCE) test.ml test_wrapper.ml
	ocamlfind ocamlc -o $@ -package oUnit -linkpkg -g str.cma $^

run-test: test
	./$^ -runner sequential -no-cache-filename -no-output-file

parencol: parencol.c
	gcc -o $@ $^

TAGS: $(SOURCE)
	ctags -e $(SOURCE)

doc: $(SOURCE)
	ocamldoc -html -d doc $(SOURCE)

.SUFFIXES:
	.ml .cmo .mli .cmi

.PHONY:
	all install-dependencies run-test clean

clean:
	rm -f *.cmi *.cmx *.o *.cmo *.cmt *.cmti *.exe infSatParser.ml infSatParser.mli infSatLexer.ml TAGS infsat top infsat-g infsat-debug infsat-prof-debug test oUnit-* parencol
