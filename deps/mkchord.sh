#!/bin/bash
pushd ~/dev/coq-dpdgraph;
  make
popd
for i in $(seq $1 $2); do
    ~/dev/coq-dpdgraph/dpd2dot -o chord$i.dot -depth $i -root chord_stabilization chord_all.dpd &&
    dot -Tsvg -o chord$i.svg chord$i.dot;
done
