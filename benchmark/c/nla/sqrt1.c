/*
 * Purpose: Compute floor(sqrt(n)) by adding successive odd numbers to form squares.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Related recurrence and invariants: Rodriguez-Carbonell and Kapur, ISSAC 2004, section
 * 5.1, Example 3. https://www.cs.unm.edu/~kapur/mypapers/issac04enric.pdf
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtrace1: t-2*a-1 == 0.
 *   vtrace1: s-(a+1)**2 == 0.
 *   vtrace1: a*a <= n.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: Encoded domain: n >= 0. At exit s>n, giving a^2 <= n < (a+1)^2.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int a, int n, int t, int s){}    

int mainQ(int n){
    vassume(n >= 0);
  
    int a,s,t;
    a=0;
    s=1;
    t=1;

    while(1){
	//assert(a*a <= n);
	//assert(t == 2*a + 1);
	//assert(s == (a + 1)*(a + 1));
	//the above 2 should be equiv to t^2 - 4*s + 2*t + 1 == 0
	vtrace1(a, n, t, s);
	if(!(s <= n)) break;
	a=a+1;
	t=t+2;
	s=s+t;
    }
    return a;
     
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}

