#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace_post(int M, int N, int P, int tCtr){}


int mainQ(int M, int N, int P){
    vassume(0 <= M);
    vassume(0 <= N);
    vassume(0 <= P);
     
    int tCtr = 0;
    int i = 0;
    int j = 0;
    int k = 0;
    while(i < N){
	j = 0;
	while(j < M){	       
	    j = j + 1;
	    k = i;
	    tCtr++;
	    while(k < P){		    
		k = k + 1;
		tCtr++;
	    }
	    i = k;
	}
	i = i + 1;
	tCtr++;
    }
    vtrace_post(M, N, P, tCtr);
    //dig2 invs:
    //l29: -N <= 0, -m <= 0, -n <= 0, n - t <= 0,
    //(N*N)*m*n + N*(m*m)*n - N*m*(n*n) - (m*m)*(n*n) - N*m*n*t + m*(n*n)*t + N*m*n - N*(n*n) - 2*m*(n*n) + N*n*t + m*n*t + (n*n)*t - n*(t*t) - (n*n) + n*t == 0, (N*N)*m*t + N*(m*m)*t - N*m*n*t - (m*m)*n*t - N*m*(t*t) + m*n*(t*t) + N*m*t - N*n*t - 2*m*n*t + N*(t*t) + m*(t*t) + n*(t*t) - (t*t*t) - n*t + (t*t) == 0

    /*
      N = 0 => t = 0 
      N <= P (N-P <= 0) => t = P + M + 1
      N > P (-N+P < 0)  =>  t = N -M(P-N)  // -N +P < 0
    */

    return 0;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
}
