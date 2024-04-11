public class H30 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]));
     }

     public static void mainQ(int n){
	  int i = 0;
	  int c = 0;

	  while (i < 1000) {
	       c = c + i;
	       i = i + 1;
	  }

	  //%%%traces: int c, int i, int n
	  //assert(c >= 0);
     }


}

