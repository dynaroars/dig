#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int flag, int u1, int u2, int u3) { 
  assert(u1 > 0 && u2 > 0 && u3 > 0);
  int a = 0;
  int b = 0;
  int j = 0;
  int w = 0;
  int x = 0;
  int y = 0;
  int z = 0;
  int i1 = 0;
  int i2 = 0; 
  int i3 = 0;

  while (i1 < u1) {
    i1++;
    int i = z;
    j = w;
    int k = 0;

    while (i < j) {
      k++;
      i++;
    }

    x = z;
    y = k;

    if (x % 2 == 1) {
      x++;
      y--;
    }

    i2 = 0;
    while (i2 < u2) {
      i2++;
      if (x % 2 == 0) {
        x += 2;
        y -= 2;
      } else {
        x--;
        y--;
      }
    }

    z++;
    w = x + y + 1;
  }

  int c = 0;
  int d = 0;
  i3 = 0;
  while (i3 < u3) {
    i3++;
    c++;
    d++;
    if (flag != 0) {
      a++;
      b++;
    } else {
      a += c;
      b += d;
    }
  }

  //%%%traces: int w, int z, int a, int b
  //assert(w >= z && a - b == 0);
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
  return 0;
}
