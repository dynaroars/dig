public class Fig4_2 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static int mainQ(int n, int m){
	  assert (n > 0);
	  assert (m > 0);
	  int v1 = n;
	  int v2 = 0;
	  int t = 0;
	  while(v1 > 0){
	       if (v2 < m) {
		    v2++;
		    v1--;
	       }else{
		    v2=0;
	       }
	       t++;
	  }

     
	  //%%%traces: int n, int m, int t, int v1, int v2
	  //dig2: l23: -t + v2 <= 0, -m + v2 <= 0, v1 == 0, m*n - m*t + n - v2 == 0, v1 - v2 <= -1
	  //Note: cannot find relationship among t and m,n  (annotated n+n/m)
	  return 0;
     }

}

