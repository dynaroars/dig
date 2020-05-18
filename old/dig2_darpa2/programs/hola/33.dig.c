#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int k, int u1, int u2, int u3) {
  int z = k;
  int x = 0;
  int y = 0;
  int i1 = 0;
  int i2 = 0; 
  int i3 = 0;

  while (i1 < u1) {
    i1++;
    int c = 0;
    i2 = 0;
    while (i2 < u2 ) {
      i2++;
      if (z == k + y - c) {
        x++;
        y++;
        c++;
      } else {
        x++;
        y--;
        c++;
      }
    }
    
    i3 = 0;
    while (i3 < u3) {
      i3++;
      x--;
      y--;
    }

    z = k + y;
  }

  //%%%traces: int x, int y
  //assert(x == y);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
  return 0;
}
