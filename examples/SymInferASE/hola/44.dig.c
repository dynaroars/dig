#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int k, int flag) {
  int j = 0;
  int n = 0;

  if (flag == 1) {
    n = 1;
  } else {
    n = 2;
  }

  int i = 0;

  while (i <= k) {
    i++;
    j = j + n;
  }
  
  //%%%traces: int j, int i, int k
  //if (flag == 1) assert(j == i);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}
