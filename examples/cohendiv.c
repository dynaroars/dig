#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x, int y, int q, int r, int a, int b){}
void vtrace2(int x, int y, int q, int r){}

int mainQ(int x, int y){
    vassume(x >= 1 && y >= 1);
    //vtrace0(x,y);  //preconditions
    int q=0;
    int r=x;
    int a=0;
    int b=0;
    while(1) {
	
        if(!(r>=y))
            break;
        a=1;
        b=y;

        while (1){
            
            assert(r >= y);
            assert(r >= 2*b);
            assert(a == 1 || a == 2);
            assert(q + r == x);
            assert(x * q + r == y );
            vtrace1(x, y, q, r, a, b);  //loop invariants
            // Invariant
            break;

            a = 2*a;
            b = 2*b;
        }
        r=r-b;
        q=q+a;
    }
    vtrace2(x, y, q, r);  //postconditions
    return q;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}




