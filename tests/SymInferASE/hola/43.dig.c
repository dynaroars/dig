#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int x, int y, int u1) { 
  assert(u1 > 0);
  assert(x != y);

  int i = 0;
  int t = y;

  while (i < u1) {
    i++;
    if (x > 0) y = y + x;
  }
  //%%%traces: int y, int t, int i
  //assert(y >= t);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
  return 0;
}
