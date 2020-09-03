#include <stdio.h>
#include <stdlib.h>
void vassume(int b){}
void vtrace(int c){}


void mainQ(void) { 
    int i = 0;
    int c = 0;

    while (i < 1000) {
	c = c + i;
	i = i + 1;
    }

    vtrace(c);
    //assert(c >= 0);
}

void main(int argc, char *argv[]) {
    mainQ();
} 
