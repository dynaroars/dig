#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int u1) {
  assert(u1 > 0);
  int i1 = 0;
  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;

  while (i1 < u1) {
    i1++;
    if (w == 1) {
      x++;
      w = 0;
    };
    if (z == 0) {
      y++;
      z = 1;
    };
  }

  //%%%traces: int x, int y
  //assert(x == y);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]));
  return 0;
}
