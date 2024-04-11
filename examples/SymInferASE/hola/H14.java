public class H14 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static void mainQ(int m, int u4) {
	  assert(m > 0);

	  int a = 0;
	  int j = 0;
	  for (j = 1; j <= m; j++) {
	       if (u4!=0)
		    a++;
	       else
		    a--;
	  }

	  //%%%traces: int a, int m
	  //assert(a >= 0 - m);
	  //assert(a <= m);
     }
}
