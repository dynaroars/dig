#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

// this is the original code that we want to generate a property
int secure_cmp(int *a, int *b, int size) {
  int res = 0;

  for (int i = 0; i < size; ++i) {
    res |= (a[i] ^ b[i]);
  }

  return (0 == res);
}

void vassume(int b) {}
/* void vtrace(int secure_cmp_a_b_5, int secure_cmp_a_b_k, */
/*             int secure_cmp_a_plus_k__b_plus_k__5_minus_k) {} */

void vtrace(int f, int f_share_1, int f_share_2){}

void mainQ(int a1, int a2, int a3, int a4, int a5, int b1, int b2, int b3,
           int b4, int b5, int divide) {
  int a[] = {a1, a2, a3, a4, a5};
  int b[] = {b1, b2, b3, b4, b5};
  vassume(divide > 0);
  int k = divide % 5;
  // generate a random number
  int f = divide * secure_cmp(a, b, 5);
  int f_share_1 = divide * secure_cmp(a, b, k);
  int f_share_2 = secure_cmp(a + k, b + k, 5 - k);
  // int result = (0 == f_share_1) && (0 == // f_share_2);
  vtrace(f, f_share_1, f_share_2);
  // goal is to prove that 
  // f = f_share_1 && f_share_2
  // or
  // f = f_share_1 * f_share_2
  printf("f = %d, f_share_1 = %d, f_share_2 = %d\n", f, f_share_1, f_share_2);
  assert(f==f_share_1*f_share_2);
}

void main(int argc, char *argv[]) {
  int a1 = atoi(argv[1]);
  int a2 = atoi(argv[2]);
  int a3 = atoi(argv[3]);
  int a4 = atoi(argv[4]);
  int a5 = atoi(argv[5]);
  int b1 = atoi(argv[6]);
  int b2 = atoi(argv[7]);
  int b3 = atoi(argv[8]);
  int b4 = atoi(argv[9]);
  int b5 = atoi(argv[10]);
  int divide = atoi(argv[11]);
  mainQ(a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, divide);
}
