public class Fig4_1 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static int mainQ(int n, int m){
	  assert(m >= 0); 
	  int x = 0;
	  int y = 0;
	  int t = 0;
	  while(x < n){
	       if(y < m){
		    y = y + 1;
	       }
	       else{
		    x = x + 1;
	       }
	       t++;
	  }
	  //%%%traces: int n, int m, int t
	  //dig2:n - t <= 0, -t <= 0    nothing useful ??
	  //NOTE: should we expect t = something here ? 
	  return 0;
     }
}

