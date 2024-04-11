public class H43 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]));
     }

     public static void mainQ(int  x, int y, int u1) { 
	  assert(u1 > 0);
	  assert(x != y);

	  int i = 0;
	  int t = y;

	  while (i < u1) {
	       i++;
	       if (x > 0) y = y + x;
	  }
	  //%%%traces: int y, int t, int i
	  //assert(y >= t);
    
     }
}
