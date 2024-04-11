public class H08 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]));
     }

     public static void mainQ(int u1, int u2, int u3) {
	  assert(u1 > 0 && u2 > 0 && u3 > 0);
	  int x = 0;
	  int y = 0;
	  int i1 = 0;
	  int i2 = 0; 
	  int i3 = 0;

	  while (i1 < u1) {
	       i1++;
	       i2++;
	       i3++;
	       if (i2 < u2) {
		    x++;
		    y += 100;
	       } else if (i3 < u3) {
		    if (x >= 4) {
			 x++;
			 y++;
		    }
		    if (x < 0) {
			 y--;
		    }
	       }
	  }
	  //%%%traces: int x, int y

	  //assert(x < 4 || y > 2);
     }
}
