#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace_post(int n, int m, int tCtr){}

int mainQ(int n, int m){
    //these assertions are based on gulwani pldi fig 4_3
    //(same as cav fig 2a).
    vassume (m > 0);
    vassume (n > m);
     
    int x = 0;
    int y = 0;
    int tCtr = 0;
    while(x < n){
	while (y < m){
	    y++;
	    tCtr++;
	}
	y=0;
	x++;
	  
    }
    vtrace_post(n, m, tCtr);
    //%%%traces: int n, int m, int t
    //dig2: -m <= -1, m*n - t == 0, m - n <= -1
    return 0;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
