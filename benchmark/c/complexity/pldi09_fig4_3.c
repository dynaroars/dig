//same as fig2a gulwani_cav09
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace_post(int n, int m, int tCtr){}

int mainQ(int n, int m){
    vassume(m > 0);
    vassume(n > m);
    int i = 0;
    int j = 0;
    int tCtr = 0;
    while(i<n){
	if (j < m) {
	    j++;
	}else{
	    j=0;
	    i++;
	}
	tCtr++;
    }
    vtrace_post(n, m, tCtr);
    //%%%traces: int n, int m, int t
    //dig2: -m <= -1, m*n + n - t == 0, m - n <= -1

    return 0;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
