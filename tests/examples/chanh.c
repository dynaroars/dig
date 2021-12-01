#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int X){}
void vtrace2(int x, int X, int i){}

void mainQ(int X) {
  int i = 0;
  int x = X;
  while (x > 0) {
    x--;
    i++;
  }

  if(i < 10){
    vtrace1(X);
  }
}
    

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]));
}
