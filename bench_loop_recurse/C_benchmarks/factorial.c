#include "seahorn/seahorn.h"

extern int unknown();

int Fact(int n) {
    if (n < 2) {
        return 1;
    } else {
        return n*Fact(n - 1);
    }
}

int main() {
    int i = 0;
    int x = 1;
    int y = 1;
    int n = unknown();
    while (i < n) {
        sassert(x == Fact(i));
        sassert(y == Fact(i+1));
        i++;
        int tmp = x;
        x = y;
        y = tmp*i;
    }
    sassert(x == Fact(n));
}
