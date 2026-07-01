#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int n, int a, int s, int t){}

int mainQ(int n){
    vassume(n >= 0);
    int a=0;
    int s=1;
    int t=1;
    while(1){
        vtrace1(n, a, s, t);
        if(!(s <= n))
            break;
        a=a+1;
        t=t+2;
        s=s+t;
    }
    return a;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}
