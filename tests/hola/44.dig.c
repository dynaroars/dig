#include <stdio.h>
#include <stdlib.h>

void vtrace(int j, int i, int k){}

void mainQ(int k, int flag) {
  int j = 0;
  int n = 0;

  if (flag == 1) {
    n = 1;
  } else {
    n = 2;
  }

  int i = 0;

  while (i <= k) {
    i++;
    j = j + n;
  }

  //%%%traces: int j, int i, int k
  vtrace(j, i, k);
  //if (flag == 1) assert(j == i);
}

void main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
}
