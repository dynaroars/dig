#include <stdio.h>
#include <stdlib.h>


void vtrace(int x, int y){}

void mainQ(int n) {
  int x = 0;
  int y = 0;
  int i = 0;
  int m = 10;

  while (i < n) {
    i++;
    x++;
    if (i % 2 == 0) y++;
  }

  //manual

  // vtrace(x, y, i, m, n);
   if (i == m) {
     vtrace(x, y);
     // assert(x == 2 * y); */
   }

}

void main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]));
}
