#!/bin/sh

set -ev

export MODE=$1

case ${MODE} in
  proofalytics)
    opam pin add verdi-chord . --yes --verbose --no-action
    opam install verdi-chord --yes --verbose --deps-only
    ./configure
    make proofalytics &
    # Output to the screen every few minutes to prevent a travis timeout
    export PID=$!
    while [[ `ps -p $PID | tail -n +2` ]]; do
	echo 'proofalyzing...'
	sleep 10
    done
    opam pin remove verdi-chord --yes --verbose
    ;;
  chord)
    opam pin add chord . --yes --verbose
    opam remove chord --yes --verbose
    opam pin remove chord --yes --verbose
    ;;
  *)
    opam pin add verdi-chord . --yes --verbose
    opam remove verdi-chord --yes --verbose
    opam pin remove verdi-chord --yes --verbose
    ;;
esac
