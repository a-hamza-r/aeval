#include "declarations.h"

//	loop peeling
//	a(i)=a(0) with actual dependence cycle, loop is vectorizable

TYPE s293(int count) {
	for (int i = 0; i < count*8; i++) {
		a[i] = a[0];
	}
  return 0;
}


/*after loop peeling and assigning a[0] to t: 

TYPE s293(int count) {
	TYPE t = a[0];
	a[0] = t;
	for (int i = 1; i < count*8; i++) {
		a[i] = t;
	}
  return 0;
}*/

int nondet();

int main() {
	int count = nondet();
	s293(count);
}