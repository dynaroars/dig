public class H19 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static void mainQ(int m, int n) {
	  assert(n >= 0);
	  assert(m >= 0);
	  assert(m < n);

	  int x = 0;
	  int y = m;

	  while (x < n) {
	       x++;
	       if (x > m) y++;
	  }

	  //%%%traces: int y, int n
	  //assert(y == n);
     }
}
