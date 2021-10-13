#include "declarations.h"

//    non-logical if's
//    arithmetic if

int s441(int count) {
if (count <= 0 || count > 10) return 1;
  for (int i = 0; i < count*8; i+=8) {
    if (d[i] < 0) {
        a[i] += b[i] * c[i];
    } else if (d[i] == 0) {
        a[i] += b[i] * b[i];
    } else {
        a[i] += c[i] * c[i];
    }

    if (d[i+1] < 0) {
        a[i+1] += b[i+1] * c[i+1];
    } else if (d[i+1] == 0) {
        a[i+1] += b[i+1] * b[i+1];
    } else {
        a[i+1] += c[i+1] * c[i+1];
    }

    if (d[i+2] < 0) {
        a[i+2] += b[i+2] * c[i+2];
    } else if (d[i+2] == 0) {
        a[i+2] += b[i+2] * b[i+2];
    } else {
        a[i+2] += c[i+2] * c[i+2];
    }

    if (d[i+3] < 0) {
        a[i+3] += b[i+3] * c[i+3];
    } else if (d[i+3] == 0) {
        a[i+3] += b[i+3] * b[i+3];
    } else {
        a[i+3] += c[i+3] * c[i+3];
    }

    if (d[i+4] < 0) {
        a[i+4] += b[i+4] * c[i+4];
    } else if (d[i+4] == 0) {
        a[i+4] += b[i+4] * b[i+4];
    } else {
        a[i+4] += c[i+4] * c[i+4];
    }

    if (d[i+5] < 0) {
        a[i+5] += b[i+5] * c[i+5];
    } else if (d[i+5] == 0) {
        a[i+5] += b[i+5] * b[i+5];
    } else {
        a[i+5] += c[i+5] * c[i+5];
    }

    if (d[i+6] < 0) {
        a[i+6] += b[i+6] * c[i+6];
    } else if (d[i+6] == 0) {
        a[i+6] += b[i+6] * b[i+6];
    } else {
        a[i+6] += c[i+6] * c[i+6];
    }

    if (d[i+7] < 0) {
        a[i+7] += b[i+7] * c[i+7];
    } else if (d[i+7] == 0) {
        a[i+7] += b[i+7] * b[i+7];
    } else {
        a[i+7] += c[i+7] * c[i+7];
    }
  }
  return 0;
}

