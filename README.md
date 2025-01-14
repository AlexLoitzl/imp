# Semantics of a (sequential) simple imperative language
Exercise for the course *Formalisms every Computer Scientist should know* thaught by [Thomas Henzinger](https://pub.ista.ac.at/~tah/) at [ISTA](https://ista.ac.at).

# Installation
Will probably run with any reasonable installation, tested with:
```
opam switch create . ocaml-base-compiler.5.2.0
opam install coq=8.20.0
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
```
