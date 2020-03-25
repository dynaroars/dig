#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int y1, int y2, int tmp){}

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
    /*@ requires y1 != 0;
        ensures y1 == 0;
        assigns y1, y2;
        //assert \forall integer i; 0 <= i < n ==> tmp == y1; y1 == y2 % y1; y2 = tmp;
     */
	while (y1 != 0) {
    vassume(y1!=0);
    vtrace(y1, y2, tmp); //failed
		tmp = y1;
		y1 = y2 % y1;
		y2 = tmp;
	}
  return tmp;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

/*@ requires (x1 > 0) && (x2 > 0);
ensures is_gcd(\result, x1, x2);
*/
