#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(void) {
  int j = 0;
  int x = 100;
  int i = 0;

  for (i = 0; i < x; i++) {
    j = j + 2;
  }
  //%%%traces: int j, int x, int i
  //assert(j == 2 * x);
}

int main(int argc, char *argv[]) {
  mainQ();
  return 0;
}
