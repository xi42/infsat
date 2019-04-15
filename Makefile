SOURCE_PRE = flags.ml timing.ml utilities.ml sortedList.ml setQueue.ml twoLayerQueue.ml batchQueue.ml syntax.ml
SOURCE_GEN = infSatParser.mli infSatParser.ml infSatLexer.ml
SOURCE_POST = grammarCommon.ml grammar.ml conversion.ml etaExpansion.ml hGrammar.ml binding.ml cfa.ml type.ml htyStore.ml environment.ml targetEnvms.ml typing.ml duplicationFactorGraph.ml saturation.ml main.ml
SOURCE = $(SOURCE_PRE) $(SOURCE_GEN) $(SOURCE_POST)

all: infsat

install-dependencies:
	opam install oUnit utop

infSatParser.mli infSatParser.ml: infSatParser.mly
	ocamlyacc infSatParser.mly
infSatLexer.ml: infSatLexer.mll
	ocamllex infSatLexer.mll

infsat: $(SOURCE) main_wrapper.ml
# consider -unsafe
	ocamlopt -inline 999 -o infsat $^

infsat-g: $(SOURCE) main_wrapper.ml
	ocamlopt -g -o infsat-prof $^

infsat-prof-debug: $(SOURCE) main_wrapper.ml
	ocamlcp -c $(SOURCE_PRE)
	ocamlc -c $(SOURCE_GEN)
	ocamlcp -c $(SOURCE_POST) main_wrapper.ml
	ocamlcp -o $@ $(filter %.cmo,$(SOURCE:.ml=.cmo)) main_wrapper.cmo

top: $(SOURCE) test.ml utop_wrapper.ml
	ocamlfind ocamlc -o top -thread -linkpkg -linkall -predicates create_toploop -package compiler-libs.toplevel,oUnit,utop -g $^

infsat-debug: $(SOURCE) main_wrapper.ml
	ocamlfind ocamlc -o infsat-debug -g $^

test: $(SOURCE) test.ml test_wrapper.ml
	ocamlfind ocamlc -o test -package oUnit -linkpkg -g $^

run-test: test
	./test -runner sequential -no-cache-filename -no-output-file

TAGS: $(SOURCE)
	ctags -e $(SOURCE)

doc: $(SOURCE)
	ocamldoc -html -d doc $(SOURCE)

.SUFFIXES:
	.ml .cmo .mli .cmi

.PHONY:
	all install-dependencies run-test clean

clean:
	rm -f *.cmi *.cmx *.o *.cmo *.cmt *.cmti *.exe infSatParser.ml infSatParser.mli infSatLexer.ml TAGS infsat top infsat-g infsat-debug infsat-prof test oUnit-*
