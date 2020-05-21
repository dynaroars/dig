#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace_post(int n, int a, int b, int tCtr){}

int mainQ(int a, int b, int n){
     int x = a;
     int z = b;
     int tCtr = 0;
     while(x < n){
	  if(z > x){
	       x++;
	  }
	  else{
	       z++;
	  }
	  tCtr++;
     }
     vtrace_post(n, a, b, tCtr); 

     //dig2: 2*n^2*t - 3*n*t^2 + t^3 - 3*n*t*x0 + 2*t^2*x0 + t*x0^2 - n*t*z0 + t^2*z0 + t*x0*z0 == 0
     //solve for t got t == 2*n - x0 - z0, t == n - x0, t == 0
     //NOTE: *** are these results correct, better, etc than the given bound of Max(0, n-x0) + Max(0, n-z0)
     //Timos: Look at comment in Fig2_1.c. Same reasoning applies here.
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
     return 0;
}
