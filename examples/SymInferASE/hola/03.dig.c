#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int i, int n, int l) {
  assert(l > 0);
  int t = 0;
  int k = 0;

  for (k = 1; k < n; k++) {

    for (i = l; i < n; i++) {
      t = t + 1;
    }

    for (i = l; i < n; i++) {
      t = t + 1;
    }
  }
  //%%%traces: int i, int k, int n, int l, int t
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
  return 0;
}
