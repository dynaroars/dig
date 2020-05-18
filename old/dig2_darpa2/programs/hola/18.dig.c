#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int a, int b, int flag) {
  int j = 0;
  for (b = 0; b < 100; ++b) {
    if (flag != 0) j = j + 1;
  }

  //%%%traces: int j, int flag, int a, int b
  //if (flag != 0) assert(j == 100);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
  return 0;
}
