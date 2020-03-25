#include <stdio.h>
#include <stdlib.h>

void vtrace(int i){}

int mainQ(int i)
{

   if (i == 0 || i == 1) return i;
   if (i == -1) return 1;

   if (i > 0) {
      return fib_rec(i - 1) + fib_rec(i - 2);
   } else {
      return fib_rec(i + 2) - fib_rec(i + 1);
   }
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}

/*@ requires SPEC_INT_MIN <= fib(i) <= SPEC_INT_MAX;
decreases \abs(i);
assigns \nothing;
ensures \result == fib(i);
*/
