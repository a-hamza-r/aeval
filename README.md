ALIEN
=====

`ALIEN` is a tool for checking equivalence between two programs that possibly have different structures. The tool takes two programs as CHCs (Constrained Horn Clauses) and outputs either the two programs are equivalent or equivalence is unknown. The tool builds on top of FREQHORN, whose implementation is given in the `rnd` branch of this repository. The tool is presented in our TACAS'23 paper (<a href="https://a-hamza-r.github.io/files/TACAS_paper.pdf">camera ready version</a>, `Lockstep Composition for Unbalanced Loops`, which has been accepted. The tool is able to prove equivalence for programs where one program contains a single loop and other can possibly contain multiple loops.

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

The tool has been evaluated on two benchmark suites:
1. Test Suite of Vectorization Compilers (TSVC) [1]
2. A subset of 24 multi-phase benchmarks in which the phases can be extracted from the loops
The directory `bench_horn_rel` contains the benchmarks for the ALIEN under the sub-directory `ALIEN_benchs`. The CHC benchmarks are to be given as input to the tool, while their C versions are also given for reference. For TSVC benchmarks, the equivalence has to be checked between `#c.smt2` and `#c_vec.smt2` programs. For split benchmarks, the equivalence has to be checked between `#.smt2` and `#_seq.smt2` programs. # represents the program name. Other sub-directories in `bench_horn_rel` contain C benchmarks that are to be input to other tools evaluated against ALIEN, including `COUNTER`, `pldi19 tool` and `LLREVE`.  

References
==========

1. S. Maleki, Y. Gao, M. J. Garzar, T. Wong, D. A. Padua, et al. An Evaluation of Vectorizing Compilers. In 2011 PACT, pages 372–382. IEEE, 2011.

