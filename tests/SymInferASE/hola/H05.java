public class H05 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static void mainQ(int flag, int n){
	  assert(n > 0);
	  int j = 0;
	  int i = 0;
	  int x = 0;
	  int y = 0;
	  int u = 0;

	  while (u < n) {
	       u++;
	       x++;
	       y++;
	       i += x;
	       j += y;
	       if (flag != 0) j += 1;
	  }
	  //%%%traces: int i, int j
  
	  //assert(j >= i);
     }
}
