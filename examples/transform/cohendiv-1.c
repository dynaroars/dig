#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
void vassume(int b)
{
}

void vtrace1(int q, int r, int a, int b, int x, int y)
{
  printf("vtrace1; %d; %d; %d; %d; %d; %d\n", q, r, a, b, x, y);
}

void vtrace2(int q, int r, int a, int b, int x, int y)
{
  printf("vtrace2; %d; %d; %d; %d; %d; %d\n", q, r, a, b, x, y);
}

int mainQ(int x, int y)
{
  assert((x >= 1) && (y >= 1));
  int q = 0;
  int r = x;
  int a = 0;
  int b = 0;
  while (1)
  {
    vtrace1(q, r, a, b, x, y);
    if (!(r >= y))
      break;
    a = 1;
    b = y;
    while (1)
    {
      vtrace2(q, r, a, b, x, y);
      if (!(r >= (2 * b)))
        break;
      a = 2 * a;
      b = 2 * b;
    }

    r = r - b;
    q = q + a;
  }

  return q;
}

void main(int argc, char **argv)
{
  mainQ(atoi(argv[1]), atoi(argv[2]));
}

