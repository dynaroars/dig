public class H38 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]));
     }

     public static void mainQ(int n){
	  int x = 0;
	  int y = 0;
	  int i = 0;

	  while (i < n) {
	       i++;
	       x++;
	       if (i % 2 == 0) y++;
	  }
	  //%%%traces: int i, int x, int y, int n
	  //if (i % 2 == 0) assert(x == 2 * y);
     }
}

