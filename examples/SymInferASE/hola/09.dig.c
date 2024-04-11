#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int j, int n, int t, int pvlen, int u1, int u2, int u3) {

  int k = 0;
  int i = 0;
  int i1 = 0;
  int i2 = 0;
  int i3 = 0;

  //  pkt = pktq->tqh_first;
  while (i1 < u1) {
    i1 = i1 + 1;
    i = i + 1;
  }

  if (i > pvlen) {
    pvlen = i;
  } else {
  }
  i = 0;

  while (i2 < u2) {
    i2 = i2 + 1;
    t = i;
    i = i + 1;
    k = k + 1;
  }

  while (i3 < u3) {
    i3 = i3 + 1;
  }

  j = 0;
  n = i;

  //%%%traces: int k
  //assert(k >= 0);
  k = k - 1;
  i = i - 1;
  j = j + 1;
  while (j < n) {
    //%%%traces: int k
    //assert(k >= 0);
    k = k - 1;
    i = i - 1;
    j = j + 1;
  }
  //PRINT_VARS();
  //PRINT_BAR(4);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), atoi(argv[5]), atoi(argv[6]), atoi(argv[7]));
  return 0;
}
