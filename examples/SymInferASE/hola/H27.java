public class H27 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]),Integer.parseInt(args[3]));
     }

     public static void mainQ(int l, int i, int k, int n) { 
	  assert(l > 0);

	  for (k = 1; k < n; k++) {

	       for (i = l; i < n; i++) {
	       }

	       for (i = l; i < n; i++) {
		    //%%%traces: int k, int l, int i, int n
		    //assert(1 <= k);
	       }
	  }
	  //%%%traces: int k, int l, int i, int n
     }
}
