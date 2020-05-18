#include <stdio.h>
#include <assert.h>

int mainQ(int a, int b){
     assert(a>=1);
     assert(b>=1);
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


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}

