#include <stdio.h>
#include <stdlib.h>
void vassume(int b) {}
void vtrace(int f_x, int f_x1, int f_x2, int x1, int x2) {}

// f(x) = x(x + 1)
int F(int x) { return x * x + x; }

void mainQ(int x1, int x2) {
  int x = x1 + x2;
  int f_x = F(x);
  int f_x1 = F(x1);
  int f_x2 = F(x2);

  vtrace(f_x, f_x1, f_x2, x1, x2);
  // goal : x1^2 + x2^2 + 2x1x2 + x1 + x2 == x^2 + x
}

void main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
}
