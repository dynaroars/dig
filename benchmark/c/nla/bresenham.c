#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int X, int Y, int x, int y, int v){}

int mainQ(int X, int Y){

    int v, x, y;
    v = 2 * Y - X;
    y = 0;
    x = 0;
    while (1) {
	//2*Y*x - 2*X*y - X + 2*Y - v == 0
	vtrace1(X,Y, x,y,v);
	if (!(x <= X))
	    break;
	
	if (v < 0) {
	    v = v + 2 * Y;
	    } else {
	    v = v + 2 * (Y - X);
	    y++;
	}
	    x++;
    }
    // 2*Y*x - 2*x*y + 2*Y - v - x + 2*y + 1 == 0
    return 0;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

