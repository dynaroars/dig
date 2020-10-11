#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int i, int n) {
  assert(n >= 0);
  int sum = 0;
  for (i = 0; i < n; ++i) {
    sum = sum + i;
  }

  //%%%traces: int sum, int i, int n
  //assert(sum >= 0);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}
