/*
 * Purpose: Compute LCM while subtracting a GCD pair and accumulating complementary coefficients.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Related family: Rodriguez-Carbonell and Kapur, ISSAC 2004, section 6 lists lcm2 and
 * cites E. W. Dijkstra, A Discipline of Programming (1976). Exact lcm1 C provenance is not
 * established. https://www.cs.unm.edu/~kapur/mypapers/issac04enric.pdf
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtrace1: x*u+y*v-a*b == 0.
 *   vtrace2: x*u+y*v-a*b == 0.
 *   vtrace3: x*u+y*v-a*b == 0.
 *   vtrace4: x*u+y*v-a*b == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: Encoded domain: a >= 1, b >= 1. At exit x=y=gcd(a,b) and u+v=lcm(a,b).
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int a, int b, int x, int y, int u, int v){}
void vtrace2(int a, int b, int x, int y, int u, int v){}
void vtrace3(int a, int b, int x, int y, int u, int v){}
void vtrace4(int a, int b, int x, int y, int u, int v){}


int mainQ(int a, int b){
    vassume(a >= 1);
    vassume(b >= 1);
    int x,y,u,v;

    x=a;
    y=b;
    u=b;
    v=0;


    while(1) {
	//assert(x*u + y*v == a*b);
	//%%%traces: int a, int b, int x, int y, int u, int v
	vtrace1(a, b, x, y, u, v);
	if (!(x!=y)) break;
	  

	while (1){
	    //%%%traces: int a, int b, int x, int y, int u, int v
	    vtrace2(a, b, x, y, u, v);
	    if(!(x>y)) break;
	    x=x-y;
	    v=v+u;
	}
    
	while (1){
	    vtrace3(a, b, x, y, u, v);
	    //%%%traces: int a, int b, int x, int y, int u, int v
	    if(!(x<y)) break;
	    y=y-x;
	    u=u+v;
	}

    }
    vtrace4(a, b, x, y, u, v);
    //x==gcd(a,b)
    return u+v; ; //lcm     
}


int main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
    return 0;
}

