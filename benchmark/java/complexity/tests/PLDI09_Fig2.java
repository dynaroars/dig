public class PLDI09_Fig2 {
    public static void vtrace0(int M, int N, int P, int i, int j, int k, int tCtr){}
    public static void vtrace1(int M, int N, int P, int i, int j, int k, int tCtr){}
    public static void vtrace2(int M, int N, int P, int i, int j, int k, int tCtr){}
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
            vtrace0(M, N, P, i, j, k, tCtr);
	    j = 0;
	    while(j<M){
                vtrace1(M, N, P, i, j, k, tCtr);
		j = j + 1;
		k = i;
		tCtr = tCtr +1;
		while (k<P){
                    vtrace2(M, N, P, i, j, k, tCtr);
		    k = k + 1;
		    tCtr = tCtr +1;
		}
		i=k;
	    }
	    i = i + 1;
	    tCtr = tCtr + 1;
	}
	return 0;
    }

}

