#!/bin/bash

cd /root/dilemma-artifact/dilemma/examples/common 
coq_makefile -f _CoqProject -o Makefile
make && make install
cd ..
coqc selection_e1.v