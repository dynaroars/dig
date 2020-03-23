public class H35 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]));
     }

     public static void mainQ(int n){
	  int x = 0;
	  while (x < n) {
	       x++;
	  }

	  //%%%traces: int x, int n
	  //if (n > 0) assert(x == n);
     }
}

