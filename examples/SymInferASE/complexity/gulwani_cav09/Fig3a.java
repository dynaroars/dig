public class Fig3a {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]));
     }

     public static int mainQ(int n){
	  int x = 0;
	  int y = 0;
	  int t = 0;
	  while(x < n){
	       y = x;
	       while (y < n){
		    t++;
		    y++;
	       }
	  
	       x=y+1;
	  }
	  //%%%traces: int n, int t
	  //dig2:  n*t - (t*t) == 0, -t <= 0, n - t <= 0
	  return 0;
     }
}
