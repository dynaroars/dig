public class H18 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]));
     }

     public static void mainQ(int a, int b, int flag) {
	  int j = 0;
	  for (b = 0; b < 100; ++b) {
	       if (flag != 0) j = j + 1;
	  }

	  //%%%traces: int j, int flag, int a, int b
	  //if (flag != 0) assert(j == 100);

     }
}
