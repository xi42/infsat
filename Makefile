SOURCE = flags.ml profiling.ml utilities.ml sortedList.ml setQueue.ml twoLayerQueue.ml batchQueue.ml syntax.ml infSatParser.mli infSatParser.ml infSatLexer.ml grammarCommon.ml grammar.ml conversion.ml stype.ml hGrammar.ml binding.ml cfa.ml type.ml htyStore.ml environment.ml typing.ml main.ml

all: infsat-debug TAGS

install-dependencies:
	opam install oUnit utop

infSatParser.mli infSatParser.ml: infSatParser.mly
	ocamlyacc infSatParser.mly
infSatLexer.ml: infSatLexer.mll
	ocamllex infSatLexer.mll

infsat: $(SOURCE) main_wrapper.ml
#	ocamlopt -pp cppo -inline 999 -unsafe -o infsat $^
	ocamlopt -inline 999 -o infsat $^

top: $(SOURCE) test.ml utop_wrapper.ml
	ocamlfind ocamlmktop -o top -thread -package utop -package oUnit -linkpkg -g $^

infsat-debug: $(SOURCE) main_wrapper.ml
	ocamlc -g -o infsat-debug $^

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
	rm -f *.cmi *.cmx *.o *.cmo *.cmt *.cmti *.exe infsat top infSatParser.ml infSatParser.mli infSatLexer.ml TAGS infsat-debug test oUnit-*
