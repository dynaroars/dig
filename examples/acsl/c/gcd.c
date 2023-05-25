#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x1, int x2, int y1, int y2){}
void vtrace2(int x1, int x2, int y1, int y2){}

int mainQ(int x1, int x2)
{
  vassume(x1 > 0 && x2 > 0);
	int y1 = x1;
	int y2 = x2;
	int tmp = 0;

	if (y1 > y2) {
		y1 = x2;
		y2 = x1;
	}
   //@ assert y1 == \min(x1, x2);
   //@ assert y2 == \max(x1, x2);
   vtrace1(x1, x2, y1, y2);

   /*@ loop invariant 0 <= y1 <= y2;
       loop invariant y2 > 0;
       loop invariant (y1 > 0)  ==> gcd(x1, x2) == gcd(y1, y2);
       loop invariant (y1 == 0) ==> gcd(x1, x2) == y2;
       loop variant y1;
	 */
	while (y1 != 0) {
    vtrace2(x1, x2, y1, y2);
		tmp = y1;
		y1 = y2 % y1;
		y2 = tmp;
	}

   return y2;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

/*@ requires x1 > 0 && x2 > 0;
assigns \nothing;
ensures is_gcd(\result, x1, x2);
*/
