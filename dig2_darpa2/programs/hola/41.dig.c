#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int n, int kt, int flag) {
  assert(n >= 0);
  int k = 1;
  if (flag != 0) {
    assert(kt >= 0);
    k = kt;
  }
  int i = 0;
  int j = 0;

  while (i <= n) {
    i++;
    j += i;
  }

  int z = k + i + j;
  //%%%traces: int z, int n, int i, int j
  //assert(z > 2 * n);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
  return 0;
}
