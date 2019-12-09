#include <stdio.h>
#include <assert.h>

int mainQ(int k){
     assert (k>=0);
     assert (k <= 30); //if too large then will cause overflow
     int y = 0;
     int x = 0;
     int c = 0;

     while(1){
	  assert(6*y*y*y*y*y + 15*y*y*y*y+ 10*y*y*y - 30*x - y == 0);
	  //printf("%d %d\n", x,y);
	  //%%%traces: int x, int y, int k

	  if (!(c < k)) break;
	  c = c +1 ;
	  y=y +1;
	  x=y*y*y*y+x;
     }
     return x;
}

int main(int argc, char **argv){
     mainQ(atoi(argv[1]));
     return 0;
}

