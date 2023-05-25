#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace0(int x, int y, int n){}
void vtrace1(int x, int y, int n){}
void mainQ(int n) {
    vassume(n >= 0); //precond
    int y = 0;
    int x = n;
    while(1){
        vtrace0(x,y,n);
        if(!(x>0)) break;
        x -= 1;
        y += 1;
    }

    vtrace1(x,y,n);
    //assert(y==n);//postcond
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]));
}
