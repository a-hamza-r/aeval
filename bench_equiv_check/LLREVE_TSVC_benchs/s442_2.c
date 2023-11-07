#include "declarations.h"

//    non-logical if's
//    computed goto

int s442(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 0; i < count*8; i+=8) {
    if (indx[i] == 1) a[i] += b[i] * b[i];
    else if (indx[i] == 2) a[i] += c[i] * c[i];
    else if (indx[i] == 3) a[i] += d[i] * d[i];
    else if (indx[i] == 4) a[i] += e[i] * e[i];

    if (indx[i+1] == 1) a[i+1] += b[i+1] * b[i+1];
    else if (indx[i+1] == 2) a[i+1] += c[i+1] * c[i+1];
    else if (indx[i+1] == 3) a[i+1] += d[i+1] * d[i+1];
    else if (indx[i+1] == 4) a[i+1] += e[i+1] * e[i+1];

    if (indx[i+2] == 1) a[i+2] += b[i+2] * b[i+2];
    else if (indx[i+2] == 2) a[i+2] += c[i+2] * c[i+2];
    else if (indx[i+2] == 3) a[i+2] += d[i+2] * d[i+2];
    else if (indx[i+2] == 4) a[i+2] += e[i+2] * e[i+2];

    if (indx[i+3] == 1) a[i+3] += b[i+3] * b[i+3];
    else if (indx[i+3] == 2) a[i+3] += c[i+3] * c[i+3];
    else if (indx[i+3] == 3) a[i+3] += d[i+3] * d[i+3];
    else if (indx[i+3] == 4) a[i+3] += e[i+3] * e[i+3];

    if (indx[i+4] == 1) a[i+4] += b[i+4] * b[i+4];
    else if (indx[i+4] == 2) a[i+4] += c[i+4] * c[i+4];
    else if (indx[i+4] == 3) a[i+4] += d[i+4] * d[i+4];
    else if (indx[i+4] == 4) a[i+4] += e[i+4] * e[i+4];

    if (indx[i+5] == 1) a[i+5] += b[i+5] * b[i+5];
    else if (indx[i+5] == 2) a[i+5] += c[i+5] * c[i+5];
    else if (indx[i+5] == 3) a[i+5] += d[i+5] * d[i+5];
    else if (indx[i+5] == 4) a[i+5] += e[i+5] * e[i+5];

    if (indx[i+6] == 1) a[i+6] += b[i+6] * b[i+6];
    else if (indx[i+6] == 2) a[i+6] += c[i+6] * c[i+6];
    else if (indx[i+6] == 3) a[i+6] += d[i+6] * d[i+6];
    else if (indx[i+6] == 4) a[i+6] += e[i+6] * e[i+6];

    if (indx[i+7] == 1) a[i+7] += b[i+7] * b[i+7];
    else if (indx[i+7] == 2) a[i+7] += c[i+7] * c[i+7];
    else if (indx[i+7] == 3) a[i+7] += d[i+7] * d[i+7];
    else if (indx[i+7] == 4) a[i+7] += e[i+7] * e[i+7];
  }
  return 0;
}

