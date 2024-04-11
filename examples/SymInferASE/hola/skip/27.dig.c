#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int l, int i, int k, int n) { 
  assert(l > 0);

  for (k = 1; k < n; k++) {

    for (i = l; i < n; i++) {
    }

    for (i = l; i < n; i++) {
      //%%%traces: int k, int l, int i, int n
      //assert(1 <= k);
    }
  }
  //%%%traces: int k, int l, int i, int n
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
  return 0;
}
