#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int i, int j, int y){}

void mainQ(int m, int n, int u1) {
  vassume(m + 1 < n);
  int i = 0;
  int j = 0;
  int k = 0;
  for (i = 0; i < n; i += 4) {

    for (j = i; j < m;) {

      if (u1) {
        //%%%traces: int j
        //vtrace(j);
        //assert(j >= 0);
        j++;
        k = 0;
        while (k < j) {
          k++;
        }
      } else {
        //%%%traces: int n, int j, int i
        vtrace(n, j, i);
        //assert(n + j + 5 > i);
        j += 2;
      }
    }
  }
  //%%%traces: int n, int j, int i
  vtrace(n, j, i);
}

void main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
}
