#!/usr/bin/env bash

set -ev

export MODE=$1

eval $(opam config env)
opam update

case ${MODE} in
  proofalytics)
    opam pin add verdi-chord . --yes --verbose --no-action
    opam install verdi-chord --yes --verbose --deps-only
    ./configure
    make proofalytics &
    # Output to the screen intermittently to prevent a Travis timeout
    export PID=$!
    while [[ `ps -p $PID | tail -n +2` ]]; do
	echo 'proofalyzing...'
	sleep 10
    done
    ;;
  chord)
    opam pin add chord . --yes --verbose
    ;;
  chord-serialized)
    opam pin add chord-serialized . --yes --verbose
    ;;
  *)
    opam pin add verdi-chord-checkproofs . --yes --verbose
    ;;
esac
