public class H41 {

  public static void vtrace (int z, int n){ }
     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]));
     }

     public static void mainQ(int n, int kt, int flag) {
	  assert(n >= 0);
	  int k = 1;
	  if (flag != 0) {
	       assert(kt >= 0);
	       k = kt;
	  }
	  int i = 0;
	  int j = 0;

	  while (i <= n) {
	       i++;
	       j += i;
	  }

	  int z = k + i + j;
	  //%%%traces: int z, int n, int i, int j
    vtrace(z, n);
	  //assert(z > 2 * n);


     }
}
