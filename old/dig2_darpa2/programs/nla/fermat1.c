#include <stdio.h>
#include <assert.h>

int mainQ(int A, int R){
     assert(A >= 1);
     assert((R-1)*(R-1) < A);
     assert(A <= R*R);
     assert(A%2 ==1); 

     int u,v,r;
     u=2*R+1;
     v=1;
     r=R*R-A;


     while (1){
	  //assert(4*(A+r) == u*u-v*v-2*u+2*v);
	  //%%%traces: int A, int R, int u, int v, int r
	  if(!(r!=0)) break;
			   
	  while (1){
	       //%%%traces: int A, int R, int u, int v, int r
	       if(!(r>0 )) break;
	       r=r-v;
	       v=v+2;
	  }
    
	  while (1){
	       //%%%traces: int A, int R, int u, int v, int r
	       if(!(r<0 )) break;
	       r=r+u;
	       u=u+2;
	  }

     }
  
     //assert(u!=v); 
     int o = (u-v)/2;
     return o;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}

