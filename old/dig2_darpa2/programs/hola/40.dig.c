#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int flag, int u1, int u2) { 
  assert(u1 > 0 && u2 > 0);

  int j = 1;
  int i = 0;
  if (flag != 0) {
    i = 0;
  } else {
    i = 1;
  }

  int i1 = 0;
  while (i1 < u1) {
    i1++;
    i += 2;
    if (i % 2 == 0) {
      j += 2;
    } else
      j++;
  }

  int a = 0;
  int b = 0;

  int i2 = 0;
  while (i2 < u2) {
    i2++;
    a++;
    b += (j - i);
  }

  //%%%traces: int a, int b, int i, int j
  //if (flag != 0) assert(a == b);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
  return 0;
}
