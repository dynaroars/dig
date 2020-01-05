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

