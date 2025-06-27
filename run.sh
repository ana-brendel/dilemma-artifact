#!/bin/bash

# set up makefiles
eval $(opam config env)
cd benchmarks/vfa_perm/common && coq_makefile -f _CoqProject -o Makefile && make && make install
cd ../../..

python3 testing_scripts/run.py $1
cd ..
touch hello.txt