#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace_post(int a, int n, int y, int x, int tCtr){}


int mainQ(int a, int n){
     int x = 0;
     int y = a;
     int tCtr = 0;
     while(x < n){
	  y++;
	  x = x + y;
	  tCtr++;
     }

     //dig2:  (y*y) - (a*a) - 2*x + y - a == 0, -x <= 0, n - x <= 0, t - y + a == 0, -y + a <= 0
     vtrace_post(a, n, y, x, tCtr);
     
     return 0;
}


void main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
}
/*same as Fig 4_3 Gulwani pldi 09*/
