#include <stdio.h>
#include <stdlib.h>

void vtrace(int result){}

int mainQ(int x)
{
  int result;
  if (x==0) {
    result = 0-0;
  }
  else if(x>0){
    result = 1 - 0;
  }
  else if (x<0) {
    result = 0 - 1;
  }
  
  //result = (x > 0) - (x < 0);
  vtrace(result);
  return result;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}
/*@ assigns \nothing;
    ensures \result == 0 || \result == 1 || \result == -1;
    behavior positive:
       assumes x > 0;
       ensures \result == 1;
    behavior zero:
       assumes x == 0;
       ensures \result == 0;
    behavior negative:
       assumes x < 0;
       ensures \result == -1;
    complete behaviors;
    disjoint behaviors;
 */
