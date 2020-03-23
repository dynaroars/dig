#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int u) {
  assert(u > 0);
  int x = 0;
  int y = 0;
  int n = 0;
  int i0 = 0;

  while (i0 < u) {
    x++;
    y++;
    i0++;
  }

  while (x != n) {
    x--;
    y--;
  }
  //%%%traces: int y, int n, int x
  //assert(y == n);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]));
  return 0;
}
