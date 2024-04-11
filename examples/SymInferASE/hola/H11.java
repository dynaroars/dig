public class H11 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]));
     }

     public static void mainQ(int n){
	  int j = 0;
	  int x = 100;
	  int i = 0;

	  for (i = 0; i < x; i++) {
	       j = j + 2;
	  }
	  //%%%traces: int j, int x, int i, int n
	  //assert(j == 2 * x);	  
     }


}

