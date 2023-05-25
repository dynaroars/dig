#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int u1) { 
  assert(u1 > 0);
  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;
  int i1 = 0;
  while (i1 < u1) {
    i1++;
    if (w % 2 == 1) {
      x++;
      w++;
    };
    if (z % 2 == 0) {
      y++;
      z++;
    };
  }
  //%%%traces: int x, int z, int y, int w
  //assert(x <= 1);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]));
  return 0;
}
