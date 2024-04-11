#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int q, int r, int a, int b, int x, int y){}

int mainQ(int x1, int x2)
{
  vassume(x1>0);
   if (x2 == 0)
      return x1;

   return gcd_rec(x2, x1 % x2);
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

/*@ requires x1 > 0;
decreases x2;
assigns \nothing;
ensures is_gcd(\result, x1, x2);
ensures \result == gcd(x1, x2);
*/
