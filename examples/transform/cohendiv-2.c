#include "civlc.cvh"
#include "stdio.h"
#include "stdlib.h"
#include "assert.h"
$input int x;
$input int y;
void vtrace1(int q, int r, int a, int b, int x, int y)
{
  printf("vtrace1: q = %d; r = %d; a = %d; b = %d; x = %d; y = %d\n", q, r, a, b, x, y);
  $pathCondition();
}

void vtrace2(int q, int r, int a, int b, int x, int y)
{
  printf("vtrace2: q = %d; r = %d; a = %d; b = %d; x = %d; y = %d\n", q, r, a, b, x, y);
  $pathCondition();
}

int mainQ(int x, int y)
{
  $assume((x >= 1) && (y >= 1));
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
  mainQ(x, y);
}

