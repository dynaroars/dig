public class H22 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]));
     }

     public static void mainQ(int u1){
	  assert(u1 > 0);
	  int x = 0;
	  int y = 0;
	  int z = 0;
	  int k = 0;
	  int i0 = 0;

	  while (i0 < u1) {
	       i0++;
	       if (k % 3 == 0) x++;
	       y++;
	       z++;
	       k = x + y + z;
	  }

	  //%%%traces: int x, int y, int z
	  //assert(x == y);
	  //assert(y == z);

     }
}

