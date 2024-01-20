#include "seahorn/seahorn.h"

extern int unknown();

int Fib(int n) {
    if (n < 2) {
        return n;
    } else {
        return Fib(n - 1) + Fib(n - 2);
    }
}

int main() {
    int i = 0;
    int x = 0;
    int y = 1;
    int n = unknown();
    while (i < n) {
        sassert(x == Fib(i));
        sassert(y == Fib(i+1));
        x = y;
        y = x + y;
        i++;
    }
    sassert(x == Fib(n));
}
