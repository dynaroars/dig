#include <stdio.h>
#include <stdlib.h>

void vtrace(int j, int i, int flag){}

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

  if (flag == 1) {
    vtrace(j, i, flag);
  }
  //assert(j == i);
}

void main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
}
