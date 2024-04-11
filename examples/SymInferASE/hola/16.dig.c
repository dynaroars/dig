#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int i, int j) { 
  int x = i;
  int y = j;

  while (x != 0) {
    x--;
    y--;
  }
  //%%%traces: int i, int j, int y
  //if (i == j) assert(y == 0);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}
