#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int n, int j, int v, int u4) {
  assert(n > 0);
  assert(n < 10);

  int c1 = 4000;
  int c2 = 2000;

  int k = 0;
  int i = 0;
  while (i < n) {
    i++;
    if (u4)
      v = 0;
    else
      v = 1;

    if (v == 0)
      k += c1;
    else
      k += c2;
  }
  
  //%%%traces: int k, int n, int j, int v
  //assert(k > n);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
  return 0;
}
