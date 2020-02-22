public class H17 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]));
     }

     public static void mainQ(int n){
	  assert(n > 0);
	  int k = 1;
	  int i = 1;
	  int j = 0;

	  while (i < n) {
	       j = 0;
	       while (j < i) {
		    k += (i - j);
		    j++;
	       }
	       i++;
	  }
	  //%%%traces: int k, int n
	  //assert(k >= n);	  

     }
}

