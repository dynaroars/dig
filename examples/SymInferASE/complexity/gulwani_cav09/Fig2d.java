public class Fig2d {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static int mainQ(int n, int m){
	  //these assertions are based on gulwani pldi fig 4_3
	  //(same as cav fig 2a).
	  assert (m > 0);
	  assert (n > m);
     
	  int x = 0;
	  int y = 0;
	  int t = 0;
	  while(x < n){
	       while (y < m){
		    t++;
		    y++;
	       }
	       y=0;
	       x++;
	  
	  }

	  //%%%traces: int n, int m, int t
	  //dig2: -m <= -1, m*n - t == 0, m - n <= -1
	  return 0;
     }


}

