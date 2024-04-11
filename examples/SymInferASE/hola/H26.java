public class H26 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]));
     }

     public static void mainQ(int u1, int u2, int u3) { 
	  assert(u1 > 0 && u2 > 0 && u3 > 0);
	  int w = 1;
	  int z = 0;
	  int x = 0;
	  int y = 0;
	  int i0 = 0;
	  int i1 = 0;
	  int i2 = 0;

	  while (i0 < u1) {
	       i0++;

	       i1 = 0;
	       while (i1 < u2) {
		    i1++;
		    if (w % 2 == 1) x++;
		    if (z % 2 == 0) y++;
	       }

	       i2 = 0;
	       while (i2 < u3) {
		    i2++;
		    z = x + y;
		    w = z + 1;
	       }
	  }

	  //%%%traces: int x, int y
	  //assert(x == y);
  
     }
}
