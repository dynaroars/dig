#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int j) {
  int i = j;
  int k = 100;
  int b = 0;
  int n = 0;
  for (n = 0; n < 2 * k; n++) {
    if (b != 0) {
      i++;
      b = 0;
    } else {
      j++;
      b = 1;
    }
  }
  //%%%traces: int i, int j, int k, int b, int n
  //assert(i == j);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]));
  return 0;
}
