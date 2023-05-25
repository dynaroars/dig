#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1_post(int m, int tCtr){}
    
void mainQ(int m) {
	int tCtr = 0;
	if (m < 0){
	    tCtr = -5;
	}
	else if (m == 0){
	    tCtr = 2;
	}
	else{
	    tCtr = m  + 5;
	}
	vtrace1_post(m, tCtr);
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]));
}
