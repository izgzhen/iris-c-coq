Iris OS
=======

## Dependencies

1. Coq 8.5pl3
2. [ssreflect 1.6.1](https://github.com/math-comp/math-comp/archive/mathcomp-1.6.1.zip)
  - `cd mathcomp; make -j8; make install`
3. [Iris 3.0](https://gitlab.mpi-sws.org/FP/iris-coq/repository/archive.zip?ref=iris-3.0.0)
  - `make -j8; make install`

## Build

Generate the make file:

```
coq_makefile -f _CoqProject -o Makefile.coq
```

Ordinary build:

```
make -f Makefile.coq
```

Quick build:

```
make -f Makefile.coq quick
```
