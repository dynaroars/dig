#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int i, int M){}
void vtrace2(int i, int M){}

void mainQ(int M) {
  vassume (0 <= M);
  int i = 0;
  while(1){
    vtrace1(i, M);
    if (!(i < M))break;
    i++;
  }
  vtrace2(i, M);
    
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]));
}
