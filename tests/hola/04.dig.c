#include <stdlib.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int y){}

void mainQ(int y) {
  int x = -50;

  while (x < 0) {
    x = x + y;
    y++;
  }

  vtrace(y);
  //assert(y > 0);
}

void main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]));
}
