public class Fig4_4 {

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
	  y=0;
	  x++;
	  while(y < m){
	       y++;
	       t++;
	  }
          t++;
     }
     //%%%traces: int n, int m, int t
     //dig2: t>= 0
     //NOTE: *** why didn't I get anything useful here ?  should t = some function of n, m ?
     // Again, there is a t++ missing for the outer loop. I ran the corrected version on DIG1 and got m*n + n - t == 0 which looks correct.
     return 0;
}

}

