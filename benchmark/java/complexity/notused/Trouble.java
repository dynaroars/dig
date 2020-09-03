public class Trouble {
    public static void vtrace1_post(int M, int N, int P, int tCtr){}
    public static void main (String[] args) {}
    public static int mainQ(int M, int N, int P){
	assert (0 <= M);
	assert (0 <= N);
	assert (0 <= P);
	int tCtr = 0;
	int i = 0;
	int j = 0;
	int k = 0;
	while(i < N){
	    j = 0;
	    while(j<M){	       
		j = j + 1;
		k = i;
		tCtr = tCtr +1;
		while (k<P){		    
		    k = k + 1;
		    tCtr = tCtr +1;
		}
		i=k;
	    }
	    i = i + 1;
	    tCtr = tCtr + 1;
	}
	vtrace1_post(M, N, P, tCtr);
	//dig2 invs:
	//l29: -N <= 0, -m <= 0, -n <= 0, n - t <= 0,
	//(N*N)*m*n + N*(m*m)*n - N*m*(n*n) - (m*m)*(n*n) - N*m*n*t + m*(n*n)*t + N*m*n - N*(n*n) - 2*m*(n*n) + N*n*t + m*n*t + (n*n)*t - n*(t*t) - (n*n) + n*t == 0, (N*N)*m*t + N*(m*m)*t - N*m*n*t - (m*m)*n*t - N*m*(t*t) + m*n*(t*t) + N*m*t - N*n*t - 2*m*n*t + N*(t*t) + m*(t*t) + n*(t*t) - (t*t*t) - n*t + (t*t) == 0

	/*
	  N = 0 => t = 0 
	  N <= P & N > 0 & M > 0  => t = P + M + 1 //(N-P <= 0)
	  N > P  =>  t = N -M(P-N)  // -N +P < 0 
	 */
	return 0;
    }

}


    

/*
t = N - M(P-N)
t = N -MP + MN
t = N + MN - MP

P < N

M=0,N=7,P=10,tCtr=7 fails -N + P < 0, tCtr == M*(N - P) + N
M=0,N=28,P=283,tCtr=28 fails -N + P < 0, tCtr == M*(N - P) + N
M=0,N=1,P=28,tCtr=1 fails -N + P < 0, tCtr == M*(N - P) + N
M=0,N=3,P=14,tCtr=3 fails -N + P < 0, tCtr == M*(N - P) + N
M=0,N=1,P=295,tCtr=1 fails -N + P < 0, tCtr == M*(N - P) + N
M=0,N=2,P=12,tCtr=2 fails -N + P < 0, tCtr == M*(N - P) + N
M=0,N=2,P=13,tCtr=2 fails -N + P < 0, tCtr == M*(N - P) + N
M=0,N=2,P=8,tCtr=2 fails -N + P < 0, tCtr == M*(N - P) + N
*/
