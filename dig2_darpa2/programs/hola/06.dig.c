#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

void mainQ(int n1, int n2) {
  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;
  int i1 = 0;
  int i2 = 0;

  while (i1 < n1) {
    
    i2 = 0;
    while (i2 < n2) {

      if (w % 2 == 1) x++;
      if (z % 2 == 0) y++;
      i2++;
    }

    z = x + y;
    w = z + 1;
    i1++;
  }
  //%%%traces: int x, int y

  //assert(x == y);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}
