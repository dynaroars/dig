public class Fig2_1 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]), Integer.parseInt(args[3]));
     }

     public static int mainQ(int x0, int y0, int n, int m){
	  int x = x0;
	  int y = y0;
	  int t = 0;
	  while(x < n){
	       if(y < m){
		    y++;
	       }
	       else{
		    x++;
	       }
	       t++;
	  }
	  //%%%traces: int n, int m, int x0, int y0, int t
     
	  //NOTE: have to manually pass in the flag -maxdeg 3 (otherwise SAGE's eqt solver seems to hang).
	  //dig2:  l17: m*n*t + (n*n)*t - m*(t*t) - 2*n*(t*t) + (t*t*t) - m*t*x0 - 2*n*t*x0 + 2*(t*t)*x0 + t*(x0*x0) - n*t*y0 + (t*t)*y0 + t*x0*y0 == 0, -t <= 0
	  //solve for t get:  [t == m + n - x0 - y0, t == n - x0, t == 0]
	  //NOTE: *** are these results correct, better, etc than the given bound of Max(0, n-x0) + Max(0, m-y0)
	  //Timos: I think they are better, because the bound Max(0, n-x0) + Max(0, m-y0) does not capture the case where x0 > n but y_0 < m.
	  //Notice that in such a case, we will never enter the loop, which is captured by t==0, but the given bound in the paper will still be m-y0.
	  return 0;
     }

}

