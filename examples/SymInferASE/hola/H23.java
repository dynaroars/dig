public class H23 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static void mainQ(int i, int n) {
	  assert(n >= 0);
	  int s = 0;
	  for (i = 0; i < n; ++i) {
	       s = s + i;
	  }

	  //%%%traces: int s, int i, int n
	  //assert(s >= 0);
     }
}
