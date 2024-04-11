public class H15 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static void mainQ(int n, int k) {
	  assert(n > 0);
	  assert(k > n);

	  int j = 0;
	  while (j < n) {
	       j++;
	       k--;
	  }
	  //%%%traces: int k, int n
	  //assert(k >= 0);
     }
}
