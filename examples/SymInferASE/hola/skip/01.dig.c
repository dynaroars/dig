#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

void mainQ(int n) {
  assert(n>0);
  int x = 1;
  int y = 1;
  int j = 0;

  while (j < n) {
    int t1 = x;
    int t2 = y;
    x = t1 + t2;
    y = t1 + t2;
    j = j + 1;
  }
  //%%%traces: int x, int y

  //assert(y >= 1);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]));
  return 0;
}
