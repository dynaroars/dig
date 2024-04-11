#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int j, int k, int n) {
  int i = 0;

  for (i = 0; i < n; i++) {

    for (j = i; j < n; j++) {

      for (k = j; k < n; k++) {
        //%%%traces: int k, int j, int n, int i 
        //assert(k >= i);
      }
    }
  }
  //%%%traces: int k, int j, int n, int i
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
  return 0;
}
