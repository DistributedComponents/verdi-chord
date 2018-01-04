#!/bin/sh

set -ev

openssl aes-256-cbc -K $encrypted_de10e8586561_key -iv $encrypted_de10e8586561_iv -in .travis/travis_rsa.enc -out .travis/travis_rsa -d
cp .travis/travis_rsa ~/.ssh
chmod 600 ~/.ssh/travis_rsa
cp .travis/ssh_config ~/.ssh/config

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
	sleep 240
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
