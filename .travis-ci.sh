opam init --yes --no-setup
eval $(opam config env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents http://opam.distributedcomponents.net
opam install coq.$COQ_VERSION coq-mathcomp-ssreflect.$SSREFLECT_VERSION \
  StructTact InfSeqExt verdi verdi-runtime ounit.2.0.0 --yes --verbose

case $MODE in
  chord)
    ./build.sh chord
    ;;
  chordshed)
    ./build.sh chordshed
    ;;
  *)
    ./build.sh
    ;;
esac
