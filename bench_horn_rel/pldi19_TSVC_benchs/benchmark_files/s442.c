#include "declarations.h"

//    non-logical if's
//    computed goto

TYPE 
__attribute__((noinline))
s442(TYPE* a, TYPE* b, TYPE *c, TYPE *d, TYPE *e, int *indx, int count) {
  for (int i = 0; i < count*8; i++) {
    switch (indx[i]) {
        case 1:  {  a[i] += b[i] * b[i];  break;  };
        case 2:  {  a[i] += c[i] * c[i];  break;  };
        case 3:  {  a[i] += d[i] * d[i];  break;  };
        case 4:  {  a[i] += e[i] * e[i];  break;  };
    }
  }
  return 0;
}

TYPE 
__attribute__((noinline))
s442_vec(TYPE* a, TYPE* b, TYPE *c, TYPE *d, TYPE *e, int *indx, int count) {
  for (int i = 0; i < count*8; i+=8) {
    switch (indx[i]) {
        case 1:  {  a[i] += b[i] * b[i];  break;  };
        case 2:  {  a[i] += c[i] * c[i];  break;  };
        case 3:  {  a[i] += d[i] * d[i];  break;  };
        case 4:  {  a[i] += e[i] * e[i];  break;  };
    }

    switch (indx[i+1]) {
        case 1:  {  a[i+1] += b[i+1] * b[i+1];  break;  };
        case 2:  {  a[i+1] += c[i+1] * c[i+1];  break;  };
        case 3:  {  a[i+1] += d[i+1] * d[i+1];  break;  };
        case 4:  {  a[i+1] += e[i+1] * e[i+1];  break;  };
    }

    switch (indx[i+2]) {
        case 1:  {  a[i+2] += b[i+2] * b[i+2];  break;  };
        case 2:  {  a[i+2] += c[i+2] * c[i+2];  break;  };
        case 3:  {  a[i+2] += d[i+2] * d[i+2];  break;  };
        case 4:  {  a[i+2] += e[i+2] * e[i+2];  break;  };
    }

    switch (indx[i+3]) {
        case 1:  {  a[i+3] += b[i+3] * b[i+3];  break;  };
        case 2:  {  a[i+3] += c[i+3] * c[i+3];  break;  };
        case 3:  {  a[i+3] += d[i+3] * d[i+3];  break;  };
        case 4:  {  a[i+3] += e[i+3] * e[i+3];  break;  };
    }

    switch (indx[i+4]) {
        case 1:  {  a[i+4] += b[i+4] * b[i+4];  break;  };
        case 2:  {  a[i+4] += c[i+4] * c[i+4];  break;  };
        case 3:  {  a[i+4] += d[i+4] * d[i+4];  break;  };
        case 4:  {  a[i+4] += e[i+4] * e[i+4];  break;  };
    }

    switch (indx[i+5]) {
        case 1:  {  a[i+5] += b[i+5] * b[i+5];  break;  };
        case 2:  {  a[i+5] += c[i+5] * c[i+5];  break;  };
        case 3:  {  a[i+5] += d[i+5] * d[i+5];  break;  };
        case 4:  {  a[i+5] += e[i+5] * e[i+5];  break;  };
    }

    switch (indx[i+6]) {
        case 1:  {  a[i+6] += b[i+6] * b[i+6];  break;  };
        case 2:  {  a[i+6] += c[i+6] * c[i+6];  break;  };
        case 3:  {  a[i+6] += d[i+6] * d[i+6];  break;  };
        case 4:  {  a[i+6] += e[i+6] * e[i+6];  break;  };
    }

    switch (indx[i+7]) {
        case 1:  {  a[i+7] += b[i+7] * b[i+7];  break;  };
        case 2:  {  a[i+7] += c[i+7] * c[i+7];  break;  };
        case 3:  {  a[i+7] += d[i+7] * d[i+7];  break;  };
        case 4:  {  a[i+7] += e[i+7] * e[i+7];  break;  };
    }
  }
  return 0;
}

int main() {
	return 0;
}