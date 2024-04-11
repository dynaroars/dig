#include <stdio.h>
#include <stdlib.h>
void vassume(int b) {}
void vtrace(int g, int h) {}

// f(x) = x(x + 1)
int F(int x) { return x * x; }

void mainQ(int x1, int x2) {
  int x = x1 + x2;
  int y = x1 - x2;
  int f_x = F(x);
  int f_y = F(y);
  int f_x1 = F(x1);
  int f_x2 = F(x2);

  vtrace(f_x*f_x - 2*f_y*f_x + f_y*f_y, f_x1*f_x2);  //  <--------------------------HERE
}

void main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
}