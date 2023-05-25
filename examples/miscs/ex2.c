#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

int a[5];
int b[5];

// this is the original code that we want to generate a property
int secure_cmp(int k, int size) {
  int res = 0;

  for (int i = k; i < size; ++i) {
    // res |= (a[i] ^ b[i]);
    if (a[i] != b[i]) {
      res = 1;
      break;
    }
  }

  if (res == 0) {
    return 1;
  } else {
    return 0;
  } 
  // return 0 == res ? 1 : 0;
  // return (0 == res);
}

void vassume(int b) {}
void vtrace(int secure_cmp_a_b_5, int secure_cmp_a_b_k,
            int secure_cmp_a_plus_k__b_plus_k__5_minus_k, int a1, int a2) {}

void mainQ(int a1, int a2, int a3, int a4, int a5, int b1, int b2, int b3,
           int b4, int b5, int divide) {
  // initialize a and b
  a[0] = a1;
  a[1] = a2;
  a[2] = a3;
  a[3] = a4;
  a[4] = a5;
  b[0] = b1;
  b[1] = b2;
  b[2] = b3;
  b[3] = b4;
  b[4] = b5;
  vassume(divide > 0);
  vassume(divide < 5);
  int k = divide;
  int f = divide * secure_cmp(0, 5);
  int f_share_1 = divide * secure_cmp(0, k);
  int f_share_2 = secure_cmp(k, 5);
  // int result = (0 == f_share_1) && (0 == // f_share_2);
  vtrace(f, f_share_1, f_share_2, a1, a2);
  // goal is to prove that
  // f = f_share_1 && f_share_2
  // or
  assert(f == f_share_1 * f_share_2);
  printf("f = %d, f_share_1 = %d, f_share_2 = %d\n", f, f_share_1, f_share_2);
}

void main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]),
        atoi(argv[5]), atoi(argv[6]), atoi(argv[7]), atoi(argv[8]),
        atoi(argv[9]), atoi(argv[10]), atoi(argv[11]));
}
