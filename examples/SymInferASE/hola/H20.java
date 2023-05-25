public class H20 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]),Integer.parseInt(args[3]),Integer.parseInt(args[4]), Integer.parseInt(args[5]));
     }

     public static void mainQ(int k, int x, int y, int i, int n, int u1) {
	  assert((x + y) == k);

	  int m = 0;
	  int j = 0;
	  while (j < n) {
	       if (j == i) {
		    x++;
		    y--;
	       } else {
		    y++;
		    x--;
	       }
	       if (u1 != 0) m = j;
	       j++;
	  }

	  //%%%traces: int x, int y, int k, int n, int m
	  //assert((x + y) == k);
	  //if (n > 0) {
	  //  assert(0 <= m);
	  //  assert(m < n);
	  //}    
     }
}
