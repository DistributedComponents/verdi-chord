Verdi Chord
===========

[![Build Status](https://api.travis-ci.org/DistributedComponents/verdi-chord.svg?branch=master)](https://travis-ci.org/DistributedComponents/verdi-chord)

An implementation of the Chord distributed lookup protocol in Coq using [the
Verdi framework](http://verdi.uwplse.org/)

Requirements
------------

 - [`Coq 8.5`](https://coq.inria.fr/coq-85)
 - [`Mathematical Components 1.6`](http://math-comp.github.io/math-comp/) (`ssreflect`)
 - [`Verdi`](https://github.com/uwplse/verdi)
 - [`StructTact`](https://github.com/uwplse/StructTact)
 - [`InfSeqExt`](https://github.com/DistributedComponents/InfSeqExt)

Building
--------

Run `./configure` in the root directory, and then run `make`.

By default, the scripts look for `StructTact`, `InfSeqExt`, and `Verdi` in
Coq's `user-contrib` directory, but this can be overridden by setting the
`StructTact_PATH`, `InfSeqExt_PATH`, and `Verdi_PATH` environment variables.
