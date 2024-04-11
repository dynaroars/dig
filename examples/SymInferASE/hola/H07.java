public class H07 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static void mainQ(int n, int u1) {
	  assert(n >= 0&& u1 > 0);

	  int a = 0;
	  int b = 0;
	  int i = 0;
	  int u = 0;

	  while (i < n) {
	       if (u < u1) {
		    a = a + 1;
		    b = b + 2;
	       } else {
		    a = a + 2;
		    b = b + 1;
	       }
	       i = i + 1;
	       u++;
	  }
	  //%%%traces: int a, int b, int n

	  //assert(a + b == 3 * n);
     }
}
