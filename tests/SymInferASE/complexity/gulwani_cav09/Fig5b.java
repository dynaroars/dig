public class Fig5b {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static int mainQ(int y0, int n){
	  int x = 0;
	  int y = y0;
	  int t = 0;
	  while(x < n){
	       y++;
	       x = x + y;
	       t++;
	  
	  }

	  //%%%traces: int y0, int n, int y, int x, int t
	  //dig2:  (y*y) - (y0*y0) - 2*x + y - y0 == 0, -x <= 0, n - x <= 0, t - y + y0 == 0, -y + y0 <= 0
     
	  return 0;
     }

}

