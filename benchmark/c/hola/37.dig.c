#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int n, int m){}

void mainQ(int n, int u1) {
  vassume(u1 > 0);
  int x = 0;
  int m = 0;

  while (x < n) {
    if (u1) {
      m = x;
    }
    x = x + 1;
  }

  //%%%traces: int n, int m, int x

  if (n > 0) {
    vtrace(n, m);
  }
  //assert(0 <= m && m < n);
}

void main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
}
