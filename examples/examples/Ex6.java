public class Ex6 {
    public static void vtrace1_post(int M, int N, int P, int tCtr){}
    public static void main (String[] args) {}
    public static int mainQ(int M, int N, int P){
	assert (0 <= M);
	assert (0 <= N);
	assert (0 <= P);
	
	int tCtr = 0;
	if (N == 0 || M == 0 || P == 0){
	    tCtr = 5;
	    vtrace1_post(M, N, P, tCtr);
	}
	
	    
	return 0;
    }
}

