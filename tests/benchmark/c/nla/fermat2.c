#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtraces1(int A, int R, int u, int v, int r){}



int mainQ(int A, int R){
    //vassume(A >= 1);
    vassume((R-1)*(R-1) < A);
    //vassume(A <= R*R);
    vassume(A%2 ==1); 

    int u,v,r;
    
    u=2*R+1;
    v=1;
    r=R*R-A;

    //assert( 4*(A+r)==u*u-v*v-2*u+2*v && v%2==1 && u%2==1 && A>=1 );
    while (1){
	//assert(4*(A + r) == u*u - v*v - 2*u + 2*v);
	//%%%traces: int A, int R, int u, int v, int r
	vtraces1(A, R, u, v, r);
	if(!(r!=0)) break;
	  
	if (r>0) {
	    r=r-v;
	    v=v+2;
	}
	else{
	    r=r+u;
	    u=u+2;
	}
    }
    //assert(u!=v);
    return (u-v)/2;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

