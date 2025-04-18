Equivalence Checking of Solidity Smart Contracts (In Progress, hence might be unstable)
========

Checking the equivalence of Smart Contracts using Constrained Horn Clauses (CHC) and SMT solvers.

Installation
============

Assumes preinstalled Boost (e.g., 1.75.0) and Gmp (e.g. 10.4.0) packages. 

* `git clone https://github.com/a-hamza-r/aeval/`
* `cd aeval`
* `git checkout equiv-check-contracts`
* `mkdir build ; cd build`
* `cmake ../`
* `cmake --build .  && cmake {PATH_TO_REPO}/aeval`
* `make -j$(nproc) equiv-check` (e.g., `make -j8 equiv-check`) -- important to run only for this target (`equiv-check`), as only `make` will result in errors. 

The binary of Equivlence Checking tool can be found at `build/tools/equiv-check/equiv-check`.
Note that `equiv-check` comes with its own version of Z3.

HowTo
==========
`./tools/equiv-check/equiv-check --preds predicatesFile file1.smt2 file2.smt2`

Where `predicatesFile` is a file containing the predicates to be checked, and `file1.smt2` and `file2.smt2` are the two files to be compared.

Benchmarks
==========

Collection of the Solidity files
https://github.com/leonardoalt/cav_2022_artifact/tree/main/regression
sol files should be encoded to smt2 format (see: https://github.com/a-hamza-r/solidity_testgen)


