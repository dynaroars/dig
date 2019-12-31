#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}


int mainQ(int a, int b){
     vassume(a>=1);
     vassume(b>=1);
     int x,y,u,v;

     x=a;
     y=b;
     u=b;
     v=a;

     while(1) {
	  //assert(x*u + y*v == 2*a*b);
	  //%%%traces: int a, int b, int x, int y, int u, int v

	  if (!(x!=y)) break;

	  if (x>y){
	       x=x-y;
	       v=v+u;
	  }
	  else {
	       y=y-x;
	       u=u+v;
	  }
     }

     //x==gcd(a,b)
     int r = (u+v)/2;
     return r; //lcm

}


void main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
}

