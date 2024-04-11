#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

void mainQ(int n) {
  assert(n > 0);
  int k = 1;
  int i = 1;
  int j = 0;

  while (i < n) {
    j = 0;
    while (j < i) {
      k += (i - j);
      j++;
    }
    i++;
  }
  //%%%traces: int k, int n
  //assert(k >= n);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]));
  return 0;
}
