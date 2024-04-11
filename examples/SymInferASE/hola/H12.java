public class H12 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]),Integer.parseInt(args[3]),Integer.parseInt(args[4]));
     }

     public static void mainQ(int x, int y, int flag, int u1, int u2) {
	  assert(u1 > 0);
	  int t = 0;
	  int s = 0;
	  int a = 0;
	  int b = 0;
	  int i1 = 0;

	  while (i1 < u1) {
	       i1++;
	       a++;
	       b++;
	       s += a;
	       t += b;
	       if (flag != 0) {
		    t += a;
	       }
	  }

	  //%%%traces: int s, int t
	  // 2s >= t
	  x = 1;
	  if (flag != 0) {
	       x = t - 2 * s + 2;
	  }

	  //%%%traces: int x, int y, int flag, int u1, int u2
	  // x <= 2
	  y = 0;
	  while (y <= x) {
	       if (u2 != 0)
		    y++;
	       else
		    y += 2;
	  }
	  //%%%traces: int x, int y, int flag, int u1, int u2
	  //assert(y <= 4);
    
     }
}
