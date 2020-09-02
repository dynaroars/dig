#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace_post(int n, int m, int tCtr){}

int mainQ(int n, int m){
    vassume(m >= 0); 
    int x = 0;
    int y = 0;
    int tCtr = 0;
    while(x < n){
	if(y < m){
	    y = y + 1;
	}
	else{
	    x = x + 1;
	}
	tCtr++;
    }
    vtrace_post(n, m, tCtr);
    //%%%traces: int n, int m, int t
    //dig2:n - t <= 0, -t <= 0    nothing useful ??
    //NOTE: should we expect t = something here ? 
    return 0;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
