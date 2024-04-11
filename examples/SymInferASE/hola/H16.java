public class H16 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static void mainQ(int i, int j) { 
	  int x = i;
	  int y = j;

	  while (x != 0) {
	       x--;
	       y--;
	  }
	  //%%%traces: int i, int j, int y
	  //if (i == j) assert(y == 0);
     }
}
