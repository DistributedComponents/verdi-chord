#!/usr/bin/env bash

set -e

PADIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

SYNC="rsync --exclude '.*' --chmod=ug=rwX --chmod=o=rX --recursive"
WEB_MACH="uwplse.org"
WEB_PATH="/var/www/verdi/chord-dash/"
RDASH="${WEB_MACH}:${WEB_PATH}"
LDASH="${PADIR}/dash/"
HOST="$([ "$TRAVIS_BRANCH" != "" ] && \
          echo "travis" || \
          hostname -s)"
BRANCH="$([ "$TRAVIS_BRANCH" != "" ] && \
            echo "$TRAVIS_BRANCH" || \
            git rev-parse --abbrev-ref HEAD)"
NONCE=$(printf "PA-%s-%s-%s-%s" \
               $(TZ="America/Los_Angeles" date "+%y%m%d") \
               $(TZ="America/Los_Angeles" date "+%H%M%S") \
               "$HOST" \
               "$BRANCH")
REPDIR="${LDASH}${NONCE}"

function main {
  echo "SYNC remote -> local"
  $SYNC "$RDASH" "$LDASH"

  mkdir "$REPDIR"
  cp index.html admit-count.txt qed-count.txt *.csv "$REPDIR"
  # publish ticks for debugging travis ci
  cp *.ticks "$REPDIR"

  echo "report,count" > "${LDASH}/admits.csv"
  echo "report,count" > "${LDASH}/qeds.csv"
  echo "report,time" > "${LDASH}/btimes.csv"
  mkindex > "${LDASH}index.html"
  echo "$(date) $(cat admit-count.txt)" >> "${LDASH}admit-log.txt"
  echo "$(date) $(cat qed-count.txt)" >> "${LDASH}qed-log.txt"

  pushd "$LDASH" > /dev/null
  ${PADIR}/plot.sh admits.csv
  ${PADIR}/plot.sh qeds.csv
  ${PADIR}/plot.sh btimes.csv
  popd > /dev/null

  echo "SYNC local  -> remote"
  $SYNC "$LDASH" "$RDASH"
}

function mkindex {
  pushd "$LDASH" > /dev/null

  cat <<EOF
<!DOCTYPE html>
<html>
<head>
  <meta charset="UTF-8">
  <title>Verdi Chord Proofalytics</title>
  <style>
    html {
      font-family: sans-serif;
    }
    body {
      margin: 30px;
    }
    h1 {
      font-size: 28pt;
      color: #4b2e83;
    }
    h2 {
      font-size: 18pt;
      color: #4b2e83;
    }
    p {
      font-size: 14pt;
    }
    .it {
      font-style: italic;
    }
    .bf {
      font-weight: bold;
    }
    ul {
      list-style-type: square;
    }
    li {
      padding-bottom: 10px;
      line-height: 150%;
    }
    .pa-link {
      text-decoration: none;
    }
    .pa-link:hover {
      font-style: italic;
    }
    circle {
      fill:black;
      stroke:black;
    }
  </style>
</head>
<body>
  <h1>Verdi Chord Proofalytics</h1>
  <img src='admits.png'><br>
  <img src='qeds.png'><br>
  <img src='btimes.png'><br>
<!--
  <script src="http://d3js.org/d3.v3.min.js" charset="utf-8"></script>
  <svg class="chart" id="admits-plot"></svg>
  <script>
    var width = 840;
    var height = 250;

    var chart = d3.select("#admits-plot")
        .attr("width", width)
        .attr("height", height)
      .append("g")
        .attr("transform",
              "translate(" + 10 + "," + 10 + ")");

    var x = d3.scale.ordinal().rangePoints([0, width - 20]);
    var y = d3.scale.linear().range([height - 20, 0]);

    d3.csv("admits.csv", function(error, data) {
      console.log("error", error);
      console.log("data", data);
      data = data.slice(0, 20);

      var dom = data.map(function(d) { return d.report; });
      dom.reverse();
      console.log("domain", dom);
      x.domain(dom);
      y.domain(d3.extent(data, function(d) { return d.count; }));

      console.log(data);

      chart.selectAll("circle")
        .data(data).enter()
        .append("circle")
        .attr("cx", function (d) { console.log(d.report, x(d.report), y(d.count)); return x(d.report); })
        .attr("cy", function (d) { console.log(d.count); return y(d.count); })
        .attr("r", "2px");
    });
  </script>
-->
  <ul>
EOF
  for rep in $(ls -r | grep 'PA-*'); do
    echo "<li>"

    d=$(echo $rep \
        | sed 's|^...\([0-9][0-9]\)\([0-9][0-9]\)\([0-9][0-9]\).*$|20\1-\2-\3|')
    t=$(echo $rep \
        | sed 's|^..........\([0-9][0-9]\)\([0-9][0-9]\)\([0-9][0-9]\).*$|\1:\2:\3|')
    h=$(echo $rep \
        | awk -W lint=fatal -F "-" \
            '{printf("%s", $4); \
              for(i=5; i<NF-1; i++) { \
                printf("-%s", $i)}}')
    b=$(echo $rep \
        | awk -W lint=fatal -F "-" '{print $NF}')
    printf "<a class='pa-link' href='%s'>%s \
              &nbsp;at&nbsp; %s \
              &nbsp;on&nbsp; %s \
              &nbsp;in&nbsp; %s</a>\n" \
           "$rep" "$d" "$t" "$h" "$b"

    echo "<br> &nbsp;"
    echo "<span class='it'>max ltac:</span> &nbsp;"
    cat "${rep}/proof-times.csv" \
      | awk -W lint=fatal -v key=2 -f "${PADIR}/csv-sort.awk" \
      | awk -W lint=fatal -F "," 'NR == 2 {print $1 " (" int($2/1000) " s)"}'

    echo "<br> &nbsp;"
    echo "<span class='it'>max qed:</span> &nbsp;"
    cat "${rep}/proof-times.csv" \
      | awk -W lint=fatal -v key=3 -f "${PADIR}/csv-sort.awk" \
      | awk -W lint=fatal -F "," 'NR == 2 {print $1 " (" int($2/1000) " s)"}'

    echo "<br> &nbsp;"
    echo "<span class='it'>build time:</span> &nbsp;"
    btime=$(awk -W lint=fatal \
              'BEGIN { FS = ","; tot = 0 }  \
               { tot += $2 }      \
               END { print tot }' \
              "${rep}/build-times.csv")
    echo "$btime s"
    echo "${rep},$btime" >> "${LDASH}btimes.csv"

    if [ -f "${rep}/admit-count.txt" ]; then
      echo "<br> &nbsp;"
      echo "<span class='it'>admits:</span> &nbsp;"
      cat "${rep}/admit-count.txt"
      echo -n "${rep}," >> "${LDASH}admits.csv"
      cat "${rep}/admit-count.txt" >> "${LDASH}admits.csv"
    fi

    if [ -f "${rep}/qed-count.txt" ]; then
      echo "<br> &nbsp;"
      echo "<span class='it'>qeds:</span> &nbsp;"
      cat "${rep}/qed-count.txt"
      echo -n "${rep}," >> "${LDASH}qeds.csv"
      cat "${rep}/qed-count.txt" >> "${LDASH}qeds.csv"
    fi

    echo "</li>"
  done
  cat <<EOF
  </ul>
</body>
</html>
EOF
  popd > /dev/null
}

main
