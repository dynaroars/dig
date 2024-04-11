#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int m, int n){}
    
void mainQ(int m, int n) {
    if (m >= 3 && m <= 200 && n >= 1 && n + 2*m == 80){
    //if (m >= 5){
        vtrace(m,n);
    }
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
