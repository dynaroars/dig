#include <stdio.h>
#include <stdlib.h>

void vtrace(int x, int n){}

void mainQ(int n) {
  int x = 0;
  while (x < n) {
    x++;
  }

  //%%%traces: int x, int n

  if (n > 0){
    vtrace(x, n);
  }
  // assert(x == n);
}

void main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]));
}
