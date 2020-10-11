#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int n) { 
  int x = 0;
  while (x < n) {
    x++;
  }

  //%%%traces: int x, int n
  //if (n > 0) assert(x == n);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]));
  return 0;
}
