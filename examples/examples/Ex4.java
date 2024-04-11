public class Ex4 {
    public static void vtrace1_post(int M, int N, int P, int tCtr){}
    public static void main (String[] args) {}
    public static int mainQ(int M, int N, int P){
	assert (0 <= M);
	assert (0 <= N);
	assert (0 <= P);
	
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
	    
	return 0;
    }
}

