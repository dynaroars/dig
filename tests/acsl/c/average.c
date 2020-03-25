#include <stdio.h>
#include <stdlib.h>

void vtrace(int a, int b, int average){}

int mainQ(int a, int b){
  int average = 0;

	int greater;
	int smaller;
	if (a > b) {
	   greater = a;
	   smaller = b;
	} else {
	   greater = b;
	   smaller = a;
	}
	if (a >= 0 && b >= 0) {
	   average = smaller + (greater - smaller) / 2;
	} else if (a < 0 && b < 0) {
	   average = greater + (smaller - greater) / 2;
	} else if ((a >= 0 && b <= 0) || (a <= 0 && b >= 0)) {
	   average = (a + b) / 2;
	}

   vtrace(a, b, average); //does not generate strong enough invariants
   return average;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}


/*@ assigns \nothing;
    ensures \result == (a+b)/2;
*/
