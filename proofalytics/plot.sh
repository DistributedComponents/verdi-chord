#!/usr/bin/env bash

name="$(basename "$1" .csv)"
tmp="$(mktemp "pa-plot-$name.XXXXXX")"

cat "$1" \
  | sed 's/PA-\([^-]*\)-[^,]*,\s*\(.*\)/\1 \2/g' \
  | sort \
  | uniq \
  | grep -v '[a-z]' \
  > "$tmp"

gnuplot <<EOF
set terminal pngcairo dashed
set output "$name.png"

set title "$name"
set xdata time
set timefmt "%y%m%d"
set format x "%b %d"
set xrange ["170909":]
set xtics rotate by 45 right
set offset graph 0.01, graph 0.01, graph 0.05, graph 0.05
plot "$tmp" using 1:2 notitle with points \
        pointtype 5 \
        linecolor rgb "#009900", \
     "$tmp" using 1:2 notitle smooth csplines with lines \
        linetype 2 \
        linewidth 2 \
        linecolor rgb "#888888" \
        dashtype "-"
EOF

if [ $? -ne 0 ]; then
  echo "Failed to plot. $1 contained:"
  cat "$1"
  echo
  echo "Massaged input to gnuplot was:"
  cat "$tmp"
  echo
fi

rm "$tmp"
