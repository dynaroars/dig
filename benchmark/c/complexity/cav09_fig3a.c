#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace_post(int n, int tCtr){}

int mainQ(int n){
    int x = 0;
    int y = 0;
    int tCtr = 0;
    while(x < n){
	y = x;
	while (y < n){
	    y++;
	    tCtr++;	       
	}
	  
	x=y+1;
    }
    vtrace_post(n, tCtr);
    //%%%traces: int n, int t
    //dig2:  n*t - (t*t) == 0, -t <= 0, n - t <= 0
    return 0;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}
