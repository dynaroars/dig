#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
//void vtrace0(int x, int y){}
void vtrace1(int x, int y, int q, int r, int a, int b){}
//void vtrace2(int q, int r, int a, int b, int x, int y){}
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
            vtrace1(x, y, q, r, a, b);  //loop invariants
            //vtrace2(q, r, a, b, x, y);  //loop invariants
            if(!(r >= 2*b))
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




