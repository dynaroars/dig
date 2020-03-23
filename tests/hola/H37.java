public class H37 {

    public static void vtrace(int n, int m) {}
     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static void mainQ(int n,  int u1) {
	  assert(u1 > 0);
	  int x = 0;
	  int m = 0;

	  while (x < n) {
	       if (u1 != 0) {
		    m = x;
	       }
	       x = x + 1;
	  }

	  //%%%traces: int n, int m, int x
	  if (n > 0) {
      vtrace(n, m);
    }
    //assert(0 <= m && m < n);
     }


}
