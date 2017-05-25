set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net

opam pin add coq $COQ_VERSION --yes --verbose

case $MODE in
  chord)
    opam pin add chord . --yes --verbose
    ;;
  *)
    opam pin add verdi-chord . --yes --verbose
    ;;
esac
