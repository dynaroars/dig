#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace_post(int id, int n, int tCtr){}

int mainQ(int id, int n){
    vassume(id >= 0);
    vassume(n > id);
    
    int tmp = id + 1;
    int tCtr = 0;

    while(tmp != id){
	if (tmp <= n) {
	    tmp = tmp + 1;
	}else{
	    tmp=0;
	}
	tCtr++;
    }
    //%%%traces: int id, int n, int t
    //dig2: n - t + 1 == 0, -id <= 0, id - n <= -1
    vtrace_post(id, n, tCtr);
    return 0;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
