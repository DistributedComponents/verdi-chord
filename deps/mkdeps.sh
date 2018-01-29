#!/bin/bash
set -e
cd "$(dirname $BASH_SOURCE[0])"

for i in $(seq $1 $2); do
    dpd2dot -o chord$i.dot -depth $i -root chord_stabilization chord_all.dpd
    echo "converting to svg"
    dot -Tsvg -o chord$i.svg chord$i.dot
done
