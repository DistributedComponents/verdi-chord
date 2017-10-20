#!/usr/bin/env bash

name="$(basename "$1" .csv)"
tmp="$(mktemp "pa-plot-$name.XXXXXX")"

cat "$1" \
  | sed 's/PA-\([^-]*\)-[^,]*,\(.*\)/\1 \2/g' \
  | sort \
  | uniq \
  | grep -v '[a-z]' \
  > "$tmp"

gnuplot <<EOF
set title "$name"
set timefmt "%y%m%d"
set xdata time
set terminal pngcairo dashed
set output "$name.png"
unset label
set xtics rotate
set offset graph 0.01, graph 0.01, graph 0.05, graph 0.05
plot "$tmp" using 1:2 notitle with points \
        pointtype 5 \
        linecolor rgb "#00aa00", \
     "$tmp" using 1:2 notitle smooth csplines with lines \
        linetype 2 \
        dashtype "-.-" \
        linecolor rgb "#888888" \
        linewidth 2
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
