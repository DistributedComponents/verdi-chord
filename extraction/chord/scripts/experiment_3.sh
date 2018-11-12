#!/bin/bash
scp rp2:/home/pi/lib/verdi-chord/shared/extraction/chord/log/chord.log db02-experiment_3.log
scp rp3:/home/pi/lib/verdi-chord/shared/extraction/chord/log/chord.log db03-experiment_3.log
scp rp4:/home/pi/lib/verdi-chord/shared/extraction/chord/log/chord.log db04-experiment_3.log
scp rp5:/home/pi/lib/verdi-chord/shared/extraction/chord/log/chord.log db05-experiment_3.log
scp rp6:/home/pi/lib/verdi-chord/shared/extraction/chord/log/chord.log db06-experiment_3.log
scp rp7:/home/pi/lib/verdi-chord/shared/extraction/chord/log/chord.log db07-experiment_3.log
scp rp8:/home/pi/lib/verdi-chord/shared/extraction/chord/log/chord.log db08-experiment_3.log
scp rp10:/home/pi/lib/verdi-chord/shared/extraction/chord/log/chord.log db10-experiment_3.log
mkdir -p experiment_3
cat db02-experiment_3.log | grep ^[0-9] > experiment_3/db02-experiment_3.log
cat db03-experiment_3.log | grep ^[0-9] > experiment_3/db03-experiment_3.log
cat db04-experiment_3.log | grep ^[0-9] > experiment_3/db04-experiment_3.log
cat db05-experiment_3.log | grep ^[0-9] > experiment_3/db05-experiment_3.log
cat db06-experiment_3.log | grep ^[0-9] > experiment_3/db06-experiment_3.log
cat db07-experiment_3.log | grep ^[0-9] > experiment_3/db07-experiment_3.log
cat db08-experiment_3.log | grep ^[0-9] > experiment_3/db08-experiment_3.log
cat db10-experiment_3.log | grep ^[0-9] > experiment_3/db10-experiment_3.log
cd experiment_3
sort -t';' -nk2 *.log | awk -F";" '{print $2","}' > data
truncate -s 0 experiment_3.json
cat ../head >> experiment_3.json
cat data >> experiment_3.json
cat ../tail >> experiment_3.json

