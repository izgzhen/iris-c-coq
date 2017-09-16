Iris C
=======

[![Build Status](https://travis-ci.org/izgzhen/iris-c-coq.svg?branch=master)](https://travis-ci.org/izgzhen/iris-c-coq)

Control-flow based language verification framework based on the Iris program logic.

[Example](theories/tests/swap.v)

[Documentation](doc/iris-c.pdf)

## Dependencies

1. Coq 8.6.1
2. ssreflect 1.6.1
4. stdpp
3. iris

[Recommended way to install dependencies](.travis.yml)

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

## Acknowledgement

Thanks to Derek Dreyer, Ralf Jung and other people in FP group
for teaching me about Iris logic and hosting me during my internship at MPI-SWS.

Thanks to Xinyu Feng and Ming Fu in USTC for discussing this work with me
and show me the code.

Also, in this source, the following files are not written by me,
but included for convenience:

- `lib/CoqLib.v`
- `lib/CpdtTactics.v`
- `lib/Integers.v`

## Licensing

All code is licensed under [3-clause BSD](https://opensource.org/licenses/BSD-3-Clause).

All doc is licensed under [CC BY-NC-SA](https://creativecommons.org/licenses/by-nc-sa/4.0/).
