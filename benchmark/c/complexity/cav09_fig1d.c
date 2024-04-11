#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace_post(int m, int tCtr){}

int mainQ(int m){

    int x = 0;
    int y = 0;
    int tCtr = 0;
    while(x < 100 && y < m){
	y++;
	tCtr++;
    }
    while(x < 100 && y >= m){
	x++;
	tCtr++;
    }

    vtrace_post(m, tCtr);
    //dig2: m*t - (t*t) - 100*m + 200*t - 10000 == 0
    //solve for t: t == m + 100, t == 100
    return 0;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}
