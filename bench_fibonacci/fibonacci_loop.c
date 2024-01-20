#include "seahorn/seahorn.h"

extern int unknown();

int main() {
    int i = 0;
    int x = 0;
    int y = 1;
    int n = unknown();
    while (i < n) {
        x = y;
        y = x + y;
        i++;
    }
    // sassert(x >= 0);
}
