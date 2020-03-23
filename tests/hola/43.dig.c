#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int y, int t, int i){}

void mainQ(int x, int y, int u1) {
  vassume(u1 > 0);
  vassume(x != y);

  int i = 0;
  int t = y;

  while (i < u1) {
    i++;
    if (x > 0) y = y + x;
  }
  //%%%traces: int y, int t, int i
  vtrace(y, t, i);
  //assert(y >= t);
}

void main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
}
