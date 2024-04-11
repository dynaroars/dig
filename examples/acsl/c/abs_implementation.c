#include <stdio.h>
#include <stdlib.h>

void vtrace(int a, int abs){}

int mainQ(int a){
  int abs;

  abs = a;
  if (a < 0) {
     abs = -abs;
  }


  vtrace(a, abs);
  return abs;

}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}


/*@ assigns \nothing;
    ensures \result >= 0;
    behavior positive:
       assumes a > 0;
       ensures \result == a;
    behavior zero:
       assumes a == 0;
       ensures \result == 0;
       ensures \result == a;
    behavior negative:
       assumes a < 0;
       ensures \result == -a;
    complete behaviors;
    disjoint behaviors;
 */
