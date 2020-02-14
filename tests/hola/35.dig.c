#include <stdio.h>
#include <stdlib.h>

void vtrace(int i, int j){}

void mainQ(int n) {
  int x = 0;
  while (x < n) {
    x++;
  }

  //%%%traces: int x, int n
  vtrace(x, n);
  //if (n > 0) assert(x == n);
}

void main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]));
}
