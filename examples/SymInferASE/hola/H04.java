public class H04 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]));
     }

     public static void mainQ(int y){
	  int x = -50;

	  while (x < 0) {
	       x = x + y;
	       y++;
	  }

	  //%%%traces: int x, int y
	  //assert(y > 0);
     }
}

