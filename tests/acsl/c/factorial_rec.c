#include <stdio.h>
#include <stdlib.h>

void vassume(int i){}
void vtrace(int q, int r, int a, int b, int x, int y){}

long mainQ(int i)
{
   vassume(i<=20);
   if (i == 0) {
      return 1;
   } else {


      return factorial_rec(i - 1) * i;
   }
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}

/*@ requires i <= 20;
decreases i;
assigns \nothing;
ensures factorial_ind(i, \result);
*/
