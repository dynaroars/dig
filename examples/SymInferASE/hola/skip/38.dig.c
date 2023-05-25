#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int n) {
  int x = 0;
  int y = 0;
  int i = 0;

  while (i < n) {
    i++;
    x++;
    if (i % 2 == 0) y++;
  }
  //%%%traces: int i, int x, int y
  //if (i % 2 == 0) assert(x == 2 * y);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]));
 return 0;
}
