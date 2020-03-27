#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x1, int x2, int min){}
void vtrace2(int x1, int x2, int i, int gcd, int min){}

int mainQ(int x1, int x2)
{
   vassume(x1 > 0 && x2 > 0);
   int min = x1 > x2 ? x2 : x1;
   //@ assert min == \min(x1, x2);
   vtrace1(x1, x2, min);
   int gcd = 1;

   /*@ loop invariant 2 <= i <= min + 1;
       loop invariant 1 <= gcd < i;
       loop invariant is_divisor(gcd, x1);
       loop invariant is_divisor(gcd, x2);
       loop invariant \forall integer j; 0 <= j < i && is_divisor(j, x1) && is_divisor(j, x2) ==> (j <= gcd);
       loop invariant gcd <= gcd(x1, x2);
       loop assigns gcd;
       loop variant min - i;
    */
   for(int i = 2; i <= min; ++i) {
     vtrace2(x1, x2, i, gcd, min); //didn't work
      if (x1 % i == 0 && x2 % i == 0) {
         gcd = i;
      }
   }

   return gcd;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

/*@ requires x1 > 0 && x2 > 0;
assigns \nothing;
ensures is_gcd(\result, x1, x2);
*/
