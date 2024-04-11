public class Fig4_3 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static int mainQ(int n, int m){
	  assert (m > 0);
	  assert (n > m);
	  int i = 0;
	  int j = 0;
	  int t = 0;
	  while(i<n){
	       if (j < m) {
		    j++;
	       }else{
		    j=0;
		    i++;
	       }
	       t++;
	  }
	  //%%%traces: int n, int m, int t
	  //dig2: -m <= -1, m*n + n - t == 0, m - n <= -1

	  return 0;
     }

}

