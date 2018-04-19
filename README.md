Verdi Chord
===========

[![Build Status](https://api.travis-ci.org/DistributedComponents/verdi-chord.svg?branch=master)](https://travis-ci.org/DistributedComponents/verdi-chord)

An implementation of the Chord distributed lookup protocol in Coq using [the
Verdi framework](http://verdi.uwplse.org/).

Requirements
------------

 - [`Coq 8.6.1`](https://coq.inria.fr/coq-86) or [`Coq 8.7`](https://coq.inria.fr/coq-87)
 - [`Mathematical Components 1.6`](http://math-comp.github.io/math-comp/) (`ssreflect`)
 - [`Verdi`](https://github.com/uwplse/verdi)
 - [`StructTact`](https://github.com/uwplse/StructTact)
 - [`InfSeqExt`](https://github.com/DistributedComponents/InfSeqExt)

Building
--------

Run `./configure` in the root directory, and then run `make`.

By default, the scripts look for `StructTact`, `InfSeqExt`, and `Verdi` in
Coq's `user-contrib` directory, but this can be overridden by setting the
`StructTact_PATH`, `InfSeqExt_PATH`, and `Verdi_PATH` environment variables. For
example, the following shell command will build Chord using a copy of StructTact
located in `../StructTact`.

```
StructTact_PATH=../StructTact ./build.sh
```

Running `chord` on a real network
---------------------------------

First, execute `make chord` from the root of this repository. This will produce
the executables `chord.native` and `client.native` in `./extraction/chord`.
To start a ring of `n` nodes, run the following.
```
extraction/chord/scripts/demo.py n
```

If you have a running node *N* at `127.0.0.2:6000` and no node at `127.0.0.1`, you can
query *N* with `client.native` as follows.
```
client.native -bind 127.0.0.1 -node 127.0.0.2:6000 -query get_ptrs
```
This will print out the predecessor and successor pointers of *N*. The following
query will ask *N* for its successor closest to the ID `md5("rdoenges")`.
```
client.native -bind 127.0.0.1 -node 127.0.0.2:6000 -query lookup 66e3ec3f16c5a8071d00b917ce3cc992
```
