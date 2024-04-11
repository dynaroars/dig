public class H06 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static void mainQ(int n1, int n2) {
	  int w = 1;
	  int z = 0;
	  int x = 0;
	  int y = 0;
	  int i1 = 0;
	  int i2 = 0;

	  while (i1 < n1) {
    
	       i2 = 0;
	       while (i2 < n2) {

		    if (w % 2 == 1) x++;
		    if (z % 2 == 0) y++;
		    i2++;
	       }

	       z = x + y;
	       w = z + 1;
	       i1++;
	  }
	  //%%%traces: int x, int y

	  //assert(x == y);
     }
}
