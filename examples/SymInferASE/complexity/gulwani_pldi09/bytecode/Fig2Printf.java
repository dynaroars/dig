public class Fig2Printf {
     public static void vtrace1(int M, int N, int P, int t){
	 System.out.printf("M %d, N %d, P %d, t %d\n",M,N,P,t);
     }
     
     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]));
     }

     public static int mainQ(int M, int N, int P){
	  assert (0 <= M);
	  assert (0 <= N);
	  assert (0 <= P);
	  int t = 0;
	  int i = 0;
	  int j = 0;
	  int k = 0;
	  while(i < N){
	       j = 0;
	       while(j < M){	       
		    j = j+1;
		    k=i;
		    t = t +1;
		    while (k<P){		    
			 k=k+1;
			 t = t +1;
		    }
		    i=k;
	       }
	       i=i+1;
	       t = t + 1;
	  }
	  vtrace1(M,N,P,t);
	  
	  //%%%traces: int M, int m, int P, int t
	  //dig2 invs:
	  //l29: -P <= 0, -m <= 0, -n <= 0, M - t <= 0, (P*P)*m*n + P*(m*m)*n - P*m*(n*n) - (m*m)*(n*n) - P*m*n*t + m*(n*n)*t + P*m*n - P*(n*n) - 2*m*(n*n) + P*n*t + m*n*t + (n*n)*t - n*(t*t) - (n*n) + n*t == 0, (P*P)*m*t + P*(m*m)*t - P*m*n*t - (m*m)*n*t - P*m*(t*t) + m*n*(t*t) + P*m*t - P*n*t - 2*m*n*t + P*(t*t) + m*(t*t) + n*(t*t) - (t*t*t) - n*t + (t*t) == 0
     
	  return 0;
     }

}



/*
N = 0  => t = 0
N <= P => t = P + M + 1
N > P  => t = N - M(P - N)


symstates:DEBUG:0. loc: vtrace1
vs: int M, int N, int P, int t, int i, int j, int k
pcs: 2 >= N, 1 < N, 0 >= M, 0 < N, 0 <= P, 0 <= N, 0 <= M
slocals: t == 2, i == 2, j == 0, k == 0
1. loc: vtrace1
vs: int M, int N, int P, int t, int i, int j, int k
pcs: 0 >= N, 0 <= P, 0 <= N, 0 <= M
slocals: t == 0, i == 0, j == 0, k == 0
2. loc: vtrace1
vs: int M, int N, int P, int t, int i, int j, int k
pcs: 3 >= N, 2 < N, 1 < N, 0 >= M, 0 < N, 0 <= P, 0 <= N, 0 <= M
slocals: t == 3, i == 3, j == 0, k == 0
3. loc: vtrace1
vs: int M, int N, int P, int t, int i, int j, int k
pcs: 1 >= N, 1 >= M, 0 >= P, 0 < M, 0 < N, 0 <= P, 0 <= N, 0 <= M
slocals: t == 2, i == 1, j == 1, k == 0
4. loc: vtrace1
vs: int M, int N, int P, int t, int i, int j, int k
pcs: 1 >= N, 0 >= M, 0 < N, 0 <= P, 0 <= N, 0 <= M
slocals: t == 1, i == 1, j == 0, k == 0



1. N = 0, M>=0, P >= 0 => t == 0, i == 0, j == 0, k == 0

4. N = 1, M==0, P >= 0 => t == 1, i == 1, j == 0, k == 0
3. N = 1, M==1, P == 0 => t == 2, i == 1, j == 1, k == 0
0. N = 2, M==0, P == 0 => t == 2, i == 2, j == 0, k == 0
2. N = 3, M==0, P >= 0 => t == 3, i == 3, j == 0, k == 0
 */
