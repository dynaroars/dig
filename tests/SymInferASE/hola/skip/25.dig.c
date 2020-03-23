#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int u1, int u2) {
  int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;
  int i1 = 0;
  int i2 = 0;

  while (i1 < u1) {
    i1++;
    i2 = 0;
    while (i2 < u2) {
      i2++;
      if (x == y)
        i++;
      else
        j++;
    }

    if (i >= j) {
      x++;
      y++;
    } else
      y++;
  }
  
  //%%%traces: int i, int j
  assert(i >= j);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}
