public class H32 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]));
     }

     public static void mainQ(int j){
	  int i = j;
	  int k = 100;
	  int b = 0;
	  int n = 0;
	  for (n = 0; n < 2 * k; n++) {
	       if (b != 0) {
		    i++;
		    b = 0;
	       } else {
		    j++;
		    b = 1;
	       }
	  }
	  //%%%traces: int i, int j, int k, int b, int n
	  //assert(i == j);
     }
}

