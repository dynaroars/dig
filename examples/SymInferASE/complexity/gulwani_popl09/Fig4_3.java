public class Fig4_3 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
	  
     }

     public static int mainQ(int n, int m){
	  assert(m >= 0);
	  assert(n >= 0);
	  int x = 0;
	  int y = 0;
	  int t = 0;
	  while(x < n){
	       if(y < m){
		    y++;
	 }
	       else{
		    y=0;
		    x++;
	       }
	       t++;
	  }
	  
	  //%%%traces: int n, int m, int y, int x, int t
	  //dig2:  y <= 0, -x <= 0, n - t <= 0, -t + x <= 0, n*t - t*x == 0, -y <= 0
	  //NOTE: *** does this eq  n*t - t*x == 0  give us anything useful about the complexity?  ***
	  //Timos: I tried this example with DIG1 and I got m*n + n - t == 0 which looks exactly right. Is there something missing above?
	  //Timos: UPDATE: With the assert statements above, the correct bound is given, although if we leave the variable x in the traces, we get this:
	  //m*x - t + x == 0, n - x == 0, y == 0, which implies m*n - t + n == 0
	  return 0;
     }

}

