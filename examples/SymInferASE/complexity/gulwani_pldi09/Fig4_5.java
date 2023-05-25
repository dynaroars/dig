public class Fig4_5 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]));
     }

     public static int mainQ(int n, int m, int j){
	  assert (m > 0);
	  assert (n > m);
	  int i = m;
	  int t = 0;
	  while(i>0 && i < n){
	       if (j > 0) {
		    i++;
	       }else{
		    i--;
	       }
	       t++;
	  }
	  //%%%traces: int n, int m, int j, int t
     
	  //NOTE: With DIG1 I got m^2*t - m*n*t + n*t^2 - t^3 == 0, whose solutions are t = n-m, t = m, t =0. They seem correct.
	  //j plays the role of a fixed truth value representing dir=fwd

	  //dig2: (m*m) - m*n + n*t - (t*t) == 0, m - n <= -1, -m <= -1
	  //NOTE: solving for the above eqt:  [t == -m + n, t == m] 
	  return 0;
     }

}

