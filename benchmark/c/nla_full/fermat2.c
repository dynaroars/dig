/*
 * Purpose: Search for a difference-of-squares factorization with one conditional
 * residual-adjustment loop.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Rodriguez-Carbonell and Kapur, ISSAC 2004, section 6 lists fermat2 and cites D. M.
 * Bressoud, Factorization and Primality Testing (1989).
 * https://www.cs.unm.edu/~kapur/mypapers/issac04enric.pdf
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtraces1: 4*(A+r)-u**2+v**2+2*u-2*v == 0.
 *   vtraces2: 4*A-u**2+v**2+2*u-2*v == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: Intended domain: positive odd A and positive initial R near sqrt(A). The file enforces
 * odd A and (R-1)^2 < A. u and v stay odd.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtraces1(int A, int R, int u, int v, int r){}
void vtraces2(int A, int R, int u, int v){}


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
    vtraces2(A, R, u, v);
    //assert(u!=v);
    return (u-v)/2;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

