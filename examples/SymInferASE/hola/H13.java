public class H13 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static void mainQ(int flag, int u1) {
	  assert(u1 > 0);
	  int j = 2;
	  int k = 0;
	  int i0 = 0;

	  while (i0 < u1) {
	       i0++;
	       if (flag != 0)
		    j = j + 4;
	       else {
		    j = j + 2;
		    k = k + 1;
	       }
	  }

	  //%%%traces: int j, int k
	  //if (k != 0) assert(j == 2 * k + 2);
     }
}
