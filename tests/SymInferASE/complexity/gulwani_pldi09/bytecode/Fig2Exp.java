public class Fig2Exp {
     public static void vtrace1(int M, int N, int P, int t){}
     public static void main (String[] args) {
     }

     public static int mainQ(int M, int N, int P){
	  //assert(N==P);
	  
	  // assert (0 <= M);
	  // assert (0 <= N);
	  // assert (0 <= P);
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



