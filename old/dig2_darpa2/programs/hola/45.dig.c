#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int flag, int u1, int u2, int u3) {
  assert(u1 > 0 && u2 > 0 && u3 > 0);
  int x = 0;
  int y = 0;
  int j = 0;
  int i = 0;
  int c = 0;
  int d = 1;
  
  int i1 = 0;
  while (i1 < u1) {
    i1++;
    x++;
    y++;
    i += x;
    j += y;
    if (flag != 0) {
      j += 1;
    }
  }

  if (j >= i)
    x = y;
  else
    x = y + 1;

  int w = 1;
  int z = 0;
  int i2 = 0;
  while (i2 < u2 ) {
    i2++;
    int i3 = 0;
    while (i3 < u3) {
      i3++;
      if (w % 2 == 1) x++;
      if (z % 2 == 0) y++;
    }

    z = x + y;
    w = z + 1;
  }

  //%%%traces: int x, int y
  //assert(x == y);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
  return 0;
}
