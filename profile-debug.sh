#!/bin/bash

SOURCES="flags.ml timing.ml utilities.ml sortedList.ml setQueue.ml twoLayerQueue.ml batchQueue.ml syntax.ml grammarCommon.ml grammar.ml conversion.ml etaExpansion.ml hGrammar.ml binding.ml cfa.ml type.ml htyStore.ml environment.ml targetEnvms.ml typing.ml duplicationFactorGraph.ml saturation.ml main.ml"

make infsat-prof-debug

./infsat-prof-debug "$@"

cp ocamlprof.dump ocamlprof.bak

for f in $SOURCES; do
  cp ocamlprof.bak ocamlprof.dump
  ocamlprof $f > ${f/%.ml/.prof.ml}
done

rm -f ocamlprof.dump ocamlprof.bak
