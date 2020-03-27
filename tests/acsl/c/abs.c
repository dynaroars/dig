#include <stdio.h>
#include <stdlib.h>

void vtrace(int a, int abs){}

int mainQ(int a){
  int abs;

  if (a < 0) {
     abs = -a;
  } else {
     abs = a;
  }

  //assert abs >= 0
  //assert if(a>0) abs == a
  //assert if(a<0) abs == -a
  //assert if(a==0) {abs == 0; abs == a}
  vtrace(a, abs);
  return abs;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}



//ACSL specifications:

/*@ //requires SPEC_INT_MIN < a <= SPEC_INT_MAX;
    requires SPEC_INT_MIN < a;
    assigns \nothing;
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
