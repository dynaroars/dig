#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int k, int x, int y, int i, int n, int u1) {
  assert((x + y) == k);

  int m = 0;
  int j = 0;
  while (j < n) {
    if (j == i) {
      x++;
      y--;
    } else {
      y++;
      x--;
    }
    if (u1) m = j;
    j++;
  }

  //%%%traces: int x, int y, int k, int n, int m
  //assert((x + y) == k);
  //if (n > 0) {
  //  assert(0 <= m);
  //  assert(m < n);
  //}
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), atoi(argv[5]), atoi(argv[6]));
  return 0;
}
