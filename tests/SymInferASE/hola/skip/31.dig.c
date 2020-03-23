#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int m, int n, int u1) {
  assert(m + 1 < n);
  int i = 0;
  int j = 0;
  int k = 0;
  for (i = 0; i < n; i += 4) {

    for (j = i; j < m;) {

      if (u1) {
        //%%%traces: int j
        //assert(j >= 0);
        j++;
        k = 0;
        while (k < j) {
          k++;
        }
      } else {
        //%%%traces: int n, int j, int i
        //assert(n + j + 5 > i);
        j += 2;
      }
    }
  }
  //%%%traces: int n, int j, int i
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
  return 0;
}
