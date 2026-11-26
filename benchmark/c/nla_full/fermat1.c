/*
 * Purpose: Search for a difference-of-squares factorization using two nested residual-adjustment
 * loops.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Related family: Rodriguez-Carbonell and Kapur, ISSAC 2004, section 6 lists fermat2 and
 * cites D. M. Bressoud, Factorization and Primality Testing (1989). Exact fermat1 C provenance is
 * not established. https://www.cs.unm.edu/~kapur/mypapers/issac04enric.pdf
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtraces1: 4*(A+r)-u**2+v**2+2*u-2*v == 0.
 *   vtraces2: 4*(A+r)-u**2+v**2+2*u-2*v == 0.
 *   vtraces3: 4*(A+r)-u**2+v**2+2*u-2*v == 0.
 *   vtraces4: 4*A-u**2+v**2+2*u-2*v == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: Intended domain: positive odd A and positive initial R near sqrt(A). The file enforces
 * odd A and (R-1)^2 < A; other bounds are commented out. u and v stay odd. At r=0,
 * 4*A=(u-v)*(u+v-2).
 */
#include <stdio.h>
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

