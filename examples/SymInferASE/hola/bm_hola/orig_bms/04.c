#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Taken from Gulwani PLDI'08:
 * Program Analysis as Constraint Solving
 */

void main() {
  int x,y;

  x = -50;
  while( x < 0 ) {
	x = x+y;
	y++;
  }
  static_assert(y>0);
}

