#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int flag, int u1) { 
  assert(u1 > 0);
  int x = 1;
  int y = 1;
  int a = 0;

  if (flag != 0)
    a = 0;
  else
    a = 1;

  int i1 = 0;
  while (i1 < u1) {
     i1++;

    if (flag != 0) {
      a = x + y;
      x++;
    } else {
      a = x + y + 1;
      y++;
    }
    if (a % 2 == 1)
      y++;
    else
      x++;
  }
  // x==y

  if (flag != 0) a++;
  //%%%traces: int a, int y, int x
  //assert(a % 2 == 1);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}
