#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int y) {
  int x = -50;

  while (x < 0) {
    x = x + y;
    y++;
  }

  //%%%traces: int x, int y
  //assert(y > 0);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]));
  return 0;
}
