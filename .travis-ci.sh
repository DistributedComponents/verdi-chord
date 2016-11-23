opam init --yes --no-setup
eval $(opam config env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.$COQ_VERSION coq-mathcomp-ssreflect.$SSREFLECT_VERSION ounit.2.0.0 --yes --verbose

pushd ..
  git clone 'https://github.com/uwplse/StructTact.git'
  pushd StructTact
    ./build.sh
  popd

  git clone 'https://github.com/DistributedComponents/InfSeqExt.git'
  pushd InfSeqExt
    ./build.sh
  popd

  git clone 'https://github.com/uwplse/verdi.git'
  pushd verdi
    ./build.sh
  popd
popd

case $MODE in
  chord)
    ./build.sh chord
    ;;
  *)
    ./build.sh
    ;;
esac
