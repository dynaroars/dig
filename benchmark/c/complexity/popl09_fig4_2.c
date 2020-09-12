#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace_post(int n, int m, int a, int b, int tCtr){}

int mainQ(int a, int b, int n, int m){
    int x = a;
    int y = b;

    int tCtr = 0;
    while(x < n){
	while(y < m){
	    y = y + 1;
	    tCtr++;
	}
	x = x + 1;
	tCtr++;
    }
    vtrace_post(n, m, a, b, tCtr);
    
    //%%%traces: int n, int m, int a, int b, int t
    //   l17: -t <= 0, m*n*t + (n*n)*t - m*(t*t) - 2*n*(t*t) + (t*t*t) - m*t*a - 2*n*t*a + 2*(t*t)*a + t*(a*a) - n*t*b + (t*t)*b + t*a*b == 0
    return 0;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
}
