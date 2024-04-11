#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int m, int n) {
  assert(n >= 0);
  assert(m >= 0);
  assert(m < n);

  int x = 0;
  int y = m;

  while (x < n) {
    x++;
    if (x > m) y++;
  }

  //%%%traces: int y, int n
  //assert(y == n);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}
