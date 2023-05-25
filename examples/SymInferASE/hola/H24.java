public class H24 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]));
     }

     public static void mainQ(int j, int k, int n) {
	  int i = 0;

	  for (i = 0; i < n; i++) {

	       for (j = i; j < n; j++) {

		    for (k = j; k < n; k++) {
			 //%%%traces: int k, int j, int n, int i 
			 //assert(k >= i);
		    }
	       }
	  }
     }
}
