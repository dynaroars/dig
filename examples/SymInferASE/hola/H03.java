public class H03 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]));
     }

     public static void mainQ(int i, int n, int l) {
	  assert(l > 0);
	  int t = 0;
	  int k = 0;

	  for (k = 1; k < n; k++) {

	       for (i = l; i < n; i++) {
		    t = t + 1;
	       }

	       for (i = l; i < n; i++) {
		    t = t + 1;
	       }
	  }
	  //%%%traces: int i, int k, int n, int l, int t
     }
}
