Chord
=====

[![Build Status](https://api.travis-ci.org/DistributedComponents/verdi-chord.svg?branch=master)](https://travis-ci.org/DistributedComponents/verdi-chord)

An implementation of the Chord distributed lookup protocol in Coq using [the
Verdi framework](http://verdi.uwplse.org/)

Requirements
------------

 - [`Coq 8.5`](https://coq.inria.fr/download)
 - [`Mathematical Components 1.6`](http://math-comp.github.io/math-comp/)
 - [`StructTact`](https://github.com/uwplse/StructTact)
 - [`InfSeqExt`](https://github.com/palmskog/InfSeqExt)

Building
--------

Use `./build.sh`. By default, it checks for `StructTact` and `InfSeqExt` in the
current parent directory, but this can be overridden by setting the
`StructTact_PATH` and/or `InfSeqExt_PATH` environment variables.
