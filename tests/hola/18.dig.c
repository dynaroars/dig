#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int flag, int j){}

void mainQ(int a, int b, int flag) {
  int j = 0;
  for (b = 0; b < 100; ++b) {
    if (flag != 0) j = j + 1;
  }

  vtrace(flag, j);
  //if (flag != 0) assert(j == 100);
}

void main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
}
