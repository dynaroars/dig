public class H33 {
    public static void vtrace(int x, int y){}
     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]),Integer.parseInt(args[3]));
     }

     public static void mainQ(int k, int u1, int u2, int u3) {
	  int z = k;
	  int x = 0;
	  int y = 0;
	  int i1 = 0;
	  int i2 = 0;
	  int i3 = 0;

	  while (i1 < u1) {
	       i1++;
	       int c = 0;
	       i2 = 0;
	       while (i2 < u2 ) {
		    i2++;
		    if (z == k + y - c) {
			 x++;
			 y++;
			 c++;
		    } else {
			 x++;
			 y--;
			 c++;
		    }
	       }

	       i3 = 0;
	       while (i3 < u3) {
		    i3++;
		    x--;
		    y--;
	       }

	       z = k + y;
	  }

	  //%%%traces: int x, int y
    vtrace(x, y);
	  //assert(x == y);

     }
}
