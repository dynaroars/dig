#include <stdio.h>
#include <assert.h>

int mainQ(int y0, int n){
     int x = 0;
     int y = y0;
     int t = 0;
     while(x < n){
	  y++;
	  x = x + y;
	  t++;
	  
     }

     //%%%traces: int y0, int n, int y, int x, int t
     //dig2:  (y*y) - (y0*y0) - 2*x + y - y0 == 0, -x <= 0, n - x <= 0, t - y + y0 == 0, -y + y0 <= 0
     
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
/*same as Fig 4_3 Gulwani pldi 09*/
