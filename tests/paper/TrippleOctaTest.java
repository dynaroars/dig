public class TrippleOctaTest {
    public static void vtrace_post(int M, int N, int P, int tCtr, int X, int Y, int Z){}
    public static void main (String[] args) {}
    public static int mainQ(int M, int N, int P){
	assert (0 <= M);
	assert (0 <= N);
	assert (0 <= P);
	int tCtr = 0;
	int i = 0;
	int j = 0;
	int k = 0;
	int X = 2*M;
	int Y= 2*N;
	int Z = 2*P;
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
	vtrace_post(M, N, P, tCtr, X, Y, Z);
	//dig2 invs:
	//l29: -N <= 0, -m <= 0, -n <= 0, n - t <= 0,
	//(N*N)*m*n + N*(m*m)*n - N*m*(n*n) - (m*m)*(n*n) - N*m*n*t + m*(n*n)*t + N*m*n - N*(n*n) - 2*m*(n*n) + N*n*t + m*n*t + (n*n)*t - n*(t*t) - (n*n) + n*t == 0, (N*N)*m*t + N*(m*m)*t - N*m*n*t - (m*m)*n*t - N*m*(t*t) + m*n*(t*t) + N*m*t - N*n*t - 2*m*n*t + N*(t*t) + m*(t*t) + n*(t*t) - (t*t*t) - n*t + (t*t) == 0

	/*
	  N = 0 => t = 0 
	  N <= P (N-P <= 0) => t = P + M + 1
	  N > P (-N+P < 0)  =>  t = N -M(P-N)  // -N +P < 0


	  #each precond simplifies to N = 0
	  # N <= 0  =>  N = 0
	  # N + P <= 0  => N = 0 ,  P = 0
	  # M + N <= 0  => N = 0 , M = 0
	  (N <= 0 | N + P <= 0 | M + N <= 0) => tCtr == 0 p

	  # N has to be > 0 (otherwise tCtr = 0)
	  # M has to be > 0 (otherwise tCtr = P + 1)
	  (N > 0 & N  <= P & M > 0) => tCtr == M + P + 1 p

	  # M <= 0  =>  M = 0
	  # N + P <= 0  => N = 0 ,  P = 0
	  # M + N <= 0  => N = 0 , M = 0
	  
	  (P < N | M <= 0 | N + P <= 0 | M + N <= 0) => tCtr == M*(N - P) + N p
	 */
	return 0;
    }

}

