#include <stdio.h>
#include <stdlib.h>

void vassume(int b) {}
void vtrace(int g, int h) {}
void vtrace3(int g, int h) {}
void vtrace1(int f_x, int f_y, int f_x1, int f_x2) {}
void vtrace2(int x1, int x2, int x, int y) {}
// f(x) = x(x + 1)
int F(int x) { return x * x; }

void mainQ(int x1, int x2) {
   vassume(-20 < x1); vassume(x1 < 20);
   vassume(-20 < x2); vassume(x2 < 20);
  
  int x = x1 + x2;
  int y = x1 - x2;
  int f_x = F(x);
  int f_y = F(y);
  int f_x1 = F(x1);
  int f_x2 = F(x2);

  int myg = f_x*f_x - 2*f_y*f_x + f_y*f_y;
  int myh = f_x1*f_x2;
  vtrace(myg, myh); // <--------------------------HERE
  //vtrace3(myg, 16*myh); // <--------------------------HERE  


  /* int f_x_f_x = f_x*f_x; */
  /* int f_y_f_x = f_y*f_x; */
  /* int f_y_f_y = f_y*f_y; */
  /* int f_x1_f_x2 = f_x1*f_x2; */

  //vtrace1(f_x,f_y,f_x1,f_x2);
  //vtrace2(x1,x2,x,y);  
}

void main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
}
