
// Cleaned version of the TSC benchmarks for verification.
// Cleaning included:
//   (1) removing benchmarking code, including any outer loops
//   (2) removing return call
//   (3) replacing floats with "TYPE" variable
//   (4) parameterizing length
//
// Criteria for selection included:
//   (i) Vectorizes with either GCC or CLANG
//      - compiled with -msse4.2 -O3
//      - gcc 4.9.2
//      - clang 3.4
//   (ii) Single loop
//   (iii) No leaf functions

#include "stdlib.h"

#define LEN 128
#define LEN2 16

#define TYPE int

// we want to be sure that the compilers but the data in the
// same memory locations so that they actually output equivalent
// code!
TYPE a[LEN] __attribute__((section ("SEGMENT_A")));
TYPE b[LEN] __attribute__((section ("SEGMENT_B")));
TYPE c[LEN] __attribute__((section ("SEGMENT_C")));
TYPE d[LEN] __attribute__((section ("SEGMENT_D")));
TYPE e[LEN] __attribute__((section ("SEGMENT_E")));
TYPE aa[LEN2][LEN2] __attribute__((section ("SEGMENT_F")));

void testing() {
  a[0] = 0;
  b[0] = 0;
  c[0] = 0;
  d[0] = 0;
  e[0] = 0;
}