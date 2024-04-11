#include <stdio.h>
#include <stdlib.h>

void vtrace(int a, int b, int result){}

int mainQ(int a, int b) {
  int result;
  if (a > b) {
    result = a-b;
  }
  else{
    result = b-a;
  }
  vtrace(a,b,result);
  return result;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

/*@ //requires \nothing;
    requires \true;
    assigns \nothing;
    ensures \result == \max(a, b) - \min(a, b);
 */
