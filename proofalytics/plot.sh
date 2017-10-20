#!/usr/bin/env bash

set -e

name=$(basename "$1" .csv)

cat "$1" \
  | tail -n +1 \
  | sed 's/PA-\([^-]*\)-[^,]*,\(.*\)/\1 \2/g' \
  | sort \
  | uniq \
  > pa-plots-tmp.csv

gnuplot <<EOF
set title "$name"
set timefmt "%y%m%d"
set xdata time
set terminal png
set output "$name.png"
unset label
set offset graph 0.01, graph 0.01, graph 0.05, graph 0.05
plot "pa-plots-tmp.csv" using 1:2 notitle, \
     "pa-plots-tmp.csv" using 1:2 notitle smooth csplines
EOF

rm pa-plots-tmp.csv
