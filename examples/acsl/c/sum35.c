#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int bound, int i, int sum){}

int mainQ(int bound)
{
  vassume(bound <= 10);
   int sum = 0;

   /*@ loop invariant (bound != 0) ==> 1 <= i <= bound;
       loop invariant (bound == 0) ==> (i == 1 && sum == 0);
       loop invariant sum <= UINT_MAX;
       loop invariant sum == sum35(i - 1);
       loop assigns i, sum;
       loop variant bound - i;
    */
   for(int i = 1; i < bound; ++i) {
     vtrace(bound, i, sum);
      if (!(i % 3) || !(i % 5)) {
         sum += i;
      }
   }

   return sum;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}
/*@ requires bound <= 10;
assigns \nothing;
ensures \result == sum35(bound - 1);
*/
