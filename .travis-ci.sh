set -ev

if [ -e "/home/travis/.opam/config" ]; then
    eval $(opam config env)
else
    opam init --compiler=${COMPILER} --yes --no-setup
    eval $(opam config env)
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
fi

opam update --yes --verbose

opam pin add coq $COQ_VERSION --yes

opam upgrade --yes --verbose

case $MODE in
  proofalytics)
    opam pin add verdi-chord . --yes --verbose --no-action
    opam install verdi-chord --yes --verbose --deps-only
    ./configure
    make proofalytics &
    # Output to the screen every 4 minutes to prevent a travis timeout
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
