#include <stdio.h>
#include <assert.h>
void mainQ(int x){
     int y = 5;
     if (x > y) x = y;
     while (1){
	  //printf("%d %d\n",x,y);
	  //%%%traces: int x, int y
	  
	  if(!(x <= 10)) break;
	  if (x >= 5) y++;
	  x++;
     }
     assert (y == 11);
}

int main(int argc, char **argv){
     mainQ(atoi(argv[1]));
     return 0;
}

