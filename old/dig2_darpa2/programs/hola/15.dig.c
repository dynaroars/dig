#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int n, int k) {
  assert(n > 0);
  assert(k > n);

  int j = 0;
  while (j < n) {
    j++;
    k--;
  }
  //%%%traces: int k, int n
  //assert(k >= 0);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}
