#include <stdio.h>
#include <stdlib.h>

void vtrace(int a, int b, int ua, int ub, int result){}

int mainQ(int a, int b) {
  int ua, ub, result;
  if (a < 0) {
    ua = -a;
  }
  else {
    ua = a;
  }

  if (b < 0) {
    ub = -b;
  }
  else {
    ub = b;
  }

   if (ua > ub) {
     result = ua - ub;
   }
   else {
     result = ub - ua;
   }

   vtrace(a, b, ua, ub, result);
   return result;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

/*@ requires \true;
    requires a > SPEC_INT_MIN; // Найдите ошибку в спецификации. Ответ.
    requires b > SPEC_INT_MIN; // Найдите ошибку в спецификации. Ответ.
    assigns \nothing;
    ensures \result == \abs(\abs(a) - \abs(b));
 */
