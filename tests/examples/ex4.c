#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1_post(int M, int N, int P, int tCtr){}
    
void mainQ(int M, int N, int P) {
    vassume (0 <= M);
    vassume (0 <= N);
    vassume (0 <= P);

    int tCtr = 0;
    if (N == 0){
	tCtr = 0;
    }
    else if (N <= P){
	tCtr = P + M + 1;
    }
    else if (N > P){ // P - N < 0  ;  -N + P < 0
	tCtr = N - M*(P-N);
    }
    vtrace1_post(M, N, P, tCtr);
    
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
}
