ALIEN
=====

A tool for checking equivalence between two programs. The tool takes two programs as CHCs (Constrained Horn Clauses) and outputs either the two programs are equivalent, non-equivalent or equivalence is unknown. The tool builds on top of FREQHORN, whose implementation is given in the `rnd` branch of this repository. The tool is presented in our FMCAD'22 paper, `Lockstep Composition of Unbalanced Loops`, which is still under review. The tool is able to prove equivalence for programs which contain unbalanced loops, i.e., the number of iterations are not necessarily the same.

Installation
============

Compiles with gcc-7 (on Linux) and clang-1001 (on Mac). Assumes preinstalled <a href="https://gmplib.org/">GMP</a>, and Boost (libboost-system1.74-dev) packages. Additionally, armadillo package to get candidates from behaviors. 

* `cd aeval ; mkdir build ; cd build`
* `cmake ../`
* `make` to build dependencies (Z3)
* `make` (again) to build ALIEN

The binary of ALIEN can be found at `build/tools/rel/`.

Benchmarks
==========

The tool has been evaluated on benchmarks from Test Suite of Vectorizing Compilers (TSVC). The directory `bench_horn_rel` contains the benchmarks for the ALIEN under the sub-directory `ALIEN_benchs`. The CHC benchmarks are to be given input to the tool, while their C versions are also given for reference. Other sub-directories in `bench_horn_rel` contain C benchmarks that are to be input to other tools evaluated against ALIEN, including `COUNTER`, `pldi19 tool` and `LLREVE`. Their comparisons are being presented in the evaluation section of the paper `Lockstep Composition of Unbalanced Loops`. 

