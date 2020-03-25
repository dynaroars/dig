#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int a, int b, int i, int sum){}

int mainQ(int a, int b)
{
  vassume(a >= 0 && b >= 0 && a<b);
   int i;
   int sum = a;

   /*@ loop invariant a < i <= (b+1);
       loop invariant sum == sum(a, i - 1);
       //loop invariant sum(a, i - 1) < SPEC_INT_MAX; Доказывается и без него
       loop variant b - i;
    */
   for(i = a + 1; i <= b; ++i) {
     vtrace(a, b, i, sum); //failed
      sum += i;
   }

   return sum;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

/*@ requires a < b;
requires a >= 0 && b >= 0;
requires sum(a, b) < SPEC_INT_MAX;
assigns \nothing;
ensures \result == sum(a, b);
*/
