#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int n, int u1) {
  assert(u1 > 0);
  int x = 0;
  int m = 0;

  while (x < n) {
    if (u1) {
      m = x;
    }
    x = x + 1;
  }

  //%%%traces: int n, int m, int x
  //if (n > 0) assert(0 <= m && m < n);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}
