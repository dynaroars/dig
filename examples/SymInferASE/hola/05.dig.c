#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int flag, int n) {
  assert(n > 0);
  int j = 0;
  int i = 0;
  int x = 0;
  int y = 0;
  int u = 0;

  while (u < n) {
    u++;
    x++;
    y++;
    i += x;
    j += y;
    if (flag != 0) j += 1;
  }
  //%%%traces: int i, int j
  
  //assert(j >= i);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}
