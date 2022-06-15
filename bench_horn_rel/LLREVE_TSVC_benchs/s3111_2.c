#include "declarations.h"

//    reductions
//    conditional sum reduction

TYPE s3111(int count) {
if (count <= 0 || count > 10) return 1;
  TYPE sum = 0;
  for (int i = 0; i < count*8; i+=8) {
      if (a[i] > 0) {
          sum += a[i];
      }

      if (a[i+1] > 0) {
          sum += a[i+1];
      }

      if (a[i+2] > 0) {
          sum += a[i+2];
      }

      if (a[i+3] > 0) {
          sum += a[i+3];
      }

      if (a[i+4] > 0) {
          sum += a[i+4];
      }

      if (a[i+5] > 0) {
          sum += a[i+5];
      }

      if (a[i+6] > 0) {
          sum += a[i+6];
      }

      if (a[i+7] > 0) {
          sum += a[i+7];
      }
  }
  return sum;
}

