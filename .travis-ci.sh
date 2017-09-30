set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net

opam pin add coq $COQ_VERSION --yes --verbose

case $MODE in
  proofalytics)
    opam pin add verdi-chord . --yes --verbose --no-action
    opam install verdi-chord --yes --verbose --deps-only
    ./configure
    make proofalytics &
    # Output to the screen every 9 minutes to prevent a travis timeout
    export PID=$!
    while [[ `ps -p $PID | tail -n +2` ]]; do
	echo 'proofalyzing...'
	sleep 540
    done
    ;;
  chord)
    opam pin add chord . --yes --verbose
    ;;
  *)
    opam pin add verdi-chord . --yes --verbose
    ;;
esac
