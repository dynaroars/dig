#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

void mainQ(int n, int u1) {
  assert(n >= 0&& u1 > 0);

  int a = 0;
  int b = 0;
  int i = 0;
  int u = 0;

  while (i < n) {
    if (u < u1) {
      a = a + 1;
      b = b + 2;
    } else {
      a = a + 2;
      b = b + 1;
    }
    i = i + 1;
    u++;
  }
  //%%%traces: int a, int b, int n

  //assert(a + b == 3 * n);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}
