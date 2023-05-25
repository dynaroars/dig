#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
//void vtrace0(int x, int y){}
void vtrace1(int x, int y){}
//void vtrace2(int q, int r, int a, int b, int x, int y){}
void vtrace2(int x, int y, int q, int r){}

int mainQ(int x, int y){
    vassume(x >= 1 && y >= 1);
    //vtrace0(x,y);  //preconditions

    while(1){
        if (!(x <= 10000))
            break;
        vtrace1(x,y);
        //1<=x <= 10000
        //1<=y
        // 1. -x <= -1
        // 2. -y <= -1
        
        x++;
    }
    
    //vtrace2(x, y, q, r);  //postconditions
    return x;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}




