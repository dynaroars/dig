#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int x, int y, int flag, int u1, int u2) {
  assert(u1 > 0);
  int t = 0;
  int s = 0;
  int a = 0;
  int b = 0;
  int i1 = 0;

  while (i1 < u1) {
    i1++;
    a++;
    b++;
    s += a;
    t += b;
    if (flag != 0) {
      t += a;
    }
  }

  //%%%traces: int s, int t
  // 2s >= t
  x = 1;
  if (flag != 0) {
    x = t - 2 * s + 2;
  }

  //%%%traces: int x
  // x <= 2
  y = 0;
  while (y <= x) {
    if (u2)
      y++;
    else
      y += 2;
  }
  //%%%traces: int y
  //assert(y <= 4);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), atoi(argv[5]));
  return 0;
}
