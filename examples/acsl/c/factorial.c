#include <stdio.h>
#include <stdlib.h>

void vtrace(int i, int f){}

long mainQ(int i)
{
   long f = 1;
   /*@ loop invariant 0 <= i;
       loop assigns f, i;
       loop variant i;
    */
   while (i) {
      f *= i--;
   }

   vtrace(i, f);
   return f;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}

/*@ requires factorial(i) <= SPEC_ULONG_MAX;
    assigns \nothing;
    ensures \result == factorial(i);
 */
