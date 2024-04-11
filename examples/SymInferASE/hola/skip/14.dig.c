#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int m, int u4) {
  assert(m > 0);

  int a = 0;
  int j = 0;
  for (j = 1; j <= m; j++) {
    if (u4)
      a++;
    else
      a--;
  }

  //%%%traces: int a, int m
  //assert(a >= 0 - m);
  //assert(a <= m);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}
