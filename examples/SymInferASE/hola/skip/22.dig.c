#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int u1) {
  assert(u1 > 0);
  int x = 0;
  int y = 0;
  int z = 0;
  int k = 0;
  int i0 = 0;

  while (i0 < u1) {
    i0++;
    if (k % 3 == 0) x++;
    y++;
    z++;
    k = x + y + z;
  }

  //%%%traces: int x, int y, int z
  //assert(x == y);
  //assert(y == z);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]));
  return 0;
}
