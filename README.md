# CoqJVM

This repository contains:

  - An executable semantics for a substantial fragment of the JVM in Coq \[1\];
  - a verifier for simple resource properties where the specifications and
    proofs are embedded in class files, written in Coq;
  - an OCaml library for dealing with JVM classfiles; and
  - a slightly modified copy of extlib 1.5 (see below).

At the time of writing, I was able to build it with OCaml 4.02.3 and
Coq 8.5rc1.  To build it you must first install ocamldsort, then run `make` in
the `extlib-1.5` directory, followed by the `ocaml-jvml-bob` directory.
The main development can then be built by `make all`.

The copy of `extlib-1.5` has been modified.  In particular (from the original svn
logs):

  - Properly implement the `header=false` option in extlib's unzip
  - Fix off-by-one error in extlib's unzip module

and there are some minor changes to the IO module.  Some of the unzip changes
may be in later versions of extlib.


\[1\] *CoqJVM: An Executable Specification of the Java Virtual Machine using
    Dependent Types*, Robert Atkey, TYPES 2007, Springer LNCS 4941, 2008.
    [DOI: 10.1007/978-3-540-68103-8_2](http://dx.doi.org/10.1007/978-3-540-68103-8_2)

