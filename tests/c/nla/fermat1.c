#include <stdio.h>
#include <assert.h>
#include <stdlib.h>

void vassume(int b){}
void vtraces1(int A, int R, int u, int v, int r){}
void vtraces2(int A, int R, int u, int v, int r){}
void vtraces3(int A, int R, int u, int v, int r){}
void vtraces4(int A, int R, int u, int v){}

int mainQ(int A, int R){
    //vassume(A >= 1);
    vassume((R-1)*(R-1) < A);
    //vassume(A <= R*R);
    vassume(A%2 ==1); 

    int u,v,r;
    u=2*R+1;
    v=1;
    r=R*R-A;


    while (1){
	//assert(4*(A+r) == u*u-v*v-2*u+2*v);
	vtraces1(A, R, u, v, r);
	
	if(!(r!=0)) break;
			   
	while (1){
	    //%%%traces: int A, int R, int u, int v, int r
	    vtraces2(A, R, u, v, r);
	    if(!(r>0 )) break;
	    r=r-v;
	    v=v+2;
	}
    
	while (1){
	    //%%%traces: int A, int R, int u, int v, int r
	    vtraces3(A, R, u, v, r);
	    if(!(r<0 )) break;
	    r=r+u;
	    u=u+2;
	}

    }
  
    //assert(u!=v); 
    //do not consider r as it is guaranteed to be 0
    vtraces4(A, R, u, v);
    return (u-v)/2;
}


int main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
    return 0;
}

