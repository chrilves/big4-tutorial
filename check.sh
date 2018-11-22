#!/bin/sh

./clean.sh

# Coq
coqc Coq/*.v

# Agda
(cd Agda && agda Cat.agda)

# Idris
(cd Idris && idris --check *.idr)

# FStar
fstar.exe FStar/Cat.fst
