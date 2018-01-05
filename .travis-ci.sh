#!/usr/bin/env bash

set -ev

export MODE=$1

eval $(opam config env)

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
    ;;
  chord)
    opam pin add chord . --yes --verbose
    ;;
  *)
    opam pin add verdi-chord . --yes --verbose
    ;;
esac
