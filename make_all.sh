#!/bin/bash

# set up makefiles
eval $(opam config env)
cd benchmarks/vfa_perm/common && coq_makefile -f _CoqProject -o Makefile && make && make install
cd ../../..

eval $(opam config env)
cd benchmarks/vfa_bagperm/common && coq_makefile -f _CoqProject -o Makefile && make && make install
cd ../../..

eval $(opam config env)
cd benchmarks/vfa_binom/common && coq_makefile -f _CoqProject -o Makefile && make && make install
cd ../../..

eval $(opam config env)
cd benchmarks/vfa_merge/common && coq_makefile -f _CoqProject -o Makefile && make && make install
cd ../../..

eval $(opam config env)
cd benchmarks/vfa_priqueue/common && coq_makefile -f _CoqProject -o Makefile && make && make install
cd ../../..

eval $(opam config env)
cd benchmarks/vfa_redblack/common && coq_makefile -f _CoqProject -o Makefile && make && make install
cd ../../..

eval $(opam config env)
cd benchmarks/vfa_searchtree/common && coq_makefile -f _CoqProject -o Makefile && make && make install
cd ../../..

eval $(opam config env)
cd benchmarks/vfa_selection/common && coq_makefile -f _CoqProject -o Makefile && make && make install
cd ../../..

eval $(opam config env)
cd benchmarks/vfa_sort/common && coq_makefile -f _CoqProject -o Makefile && make && make install
cd ../../..

eval $(opam config env)
cd benchmarks/vfa_trie/common && coq_makefile -f _CoqProject -o Makefile && make && make install
cd ../../..

eval $(opam config env)
cd benchmarks/lia/implications/common && coq_makefile -f _CoqProject -o Makefile && make && make install
cd ../../..