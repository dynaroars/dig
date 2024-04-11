#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int z, int n){}

void mainQ(int n, int kt, int flag) {
  vassume(n >= 0);
  int k = 1;
  if (flag != 0) {
    vassume(kt >= 0);
    k = kt;
  }
  int i = 0;
  int j = 0;

  while (i <= n) {
    i++;
    j += i;
  }

  int z = k + i + j;
  //%%%traces: int z, int n, int i, int j
  vtrace(z, n);
  //assert(z > 2 * n);
}

void main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
}
