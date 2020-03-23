#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int flag, int u1) {
  assert(u1 > 0);
  int j = 2;
  int k = 0;
  int i0 = 0;

  while (i0 < u1) {
    i0++;
    if (flag != 0)
      j = j + 4;
    else {
      j = j + 2;
      k = k + 1;
    }
  }

  //%%%traces: int j, int k
  //if (k != 0) assert(j == 2 * k + 2);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}
