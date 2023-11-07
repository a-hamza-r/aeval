#include "declarations.h"

//    control flow
//    tests for recognition of loop independent dependences
//    between statements in mutually exclusive regions.

int s1161(int count)
{
if (count <= 0 || count > 10) return 1;
    if (c[0] < 0) {
        b[0] = a[0] + d[0] * d[0];
    }
    else {
        a[0] = c[0] + d[0] * e[0];
    }
    if (c[1] < 0) {
        b[1] = a[1] + d[1] * d[1];
    }
    else {
        a[1] = c[1] + d[1] * e[1];
    }
    if (c[2] < 0) {
        b[2] = a[2] + d[2] * d[2];
    }
    else {
        a[2] = c[2] + d[2] * e[2];
    }
    if (c[3] < 0) {
        b[3] = a[3] + d[3] * d[3];
    }
    else {
        a[3] = c[3] + d[3] * e[3];
    }
    if (c[4] < 0) {
        b[4] = a[4] + d[4] * d[4];
    }
    else {
        a[4] = c[4] + d[4] * e[4];
    }
    if (c[5] < 0) {
        b[5] = a[5] + d[5] * d[5];
    }
    else {
        a[5] = c[5] + d[5] * e[5];
    }
    if (c[6] < 0) {
        b[6] = a[6] + d[6] * d[6];
    }
    else {
        a[6] = c[6] + d[6] * e[6];
    }
    if (c[7] < 0) {
        b[7] = a[7] + d[7] * d[7];
    }
    else {
        a[7] = c[7] + d[7] * e[7];
    }

    for (int i = 7; i < count*8-1; i+=8) {
        if (c[i] < 0) {
            b[i] = a[i] + d[i] * d[i];
        }
        else {
            a[i] = c[i] + d[i] * e[i];
        }
        if (c[i+1] < 0) {
            b[i+1] = a[i+1] + d[i+1] * d[i+1];
        }
        else {
            a[i+1] = c[i+1] + d[i+1] * e[i+1];
        }
        if (c[i+2] < 0) {
            b[i+2] = a[i+2] + d[i+2] * d[i+2];
        }
        else {
            a[i+2] = c[i+2] + d[i+2] * e[i+2];
        }
        if (c[i+3] < 0) {
            b[i+3] = a[i+3] + d[i+3] * d[i+3];
        }
        else {
            a[i+3] = c[i+3] + d[i+3] * e[i+3];
        }
        if (c[i+4] < 0) {
            b[i+4] = a[i+4] + d[i+4] * d[i+4];
        }
        else {
            a[i+4] = c[i+4] + d[i+4] * e[i+4];
        }
        if (c[i+5] < 0) {
            b[i+5] = a[i+5] + d[i+5] * d[i+5];
        }
        else {
            a[i+5] = c[i+5] + d[i+5] * e[i+5];
        }
        if (c[i+6] < 0) {
            b[i+6] = a[i+6] + d[i+6] * d[i+6];
        }
        else {
            a[i+6] = c[i+6] + d[i+6] * e[i+6];
        }
        if (c[i+7] < 0) {
            b[i+7] = a[i+7] + d[i+7] * d[i+7];
        }
        else {
            a[i+7] = c[i+7] + d[i+7] * e[i+7];
        }
    }
    return 0;
}