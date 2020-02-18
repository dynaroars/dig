public class H38 {
  public static void vtrace(int x, int y){}
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
    //vtrace(i, x, y, n);
	  if (i % 2 == 0){
      vtrace(x,y);
      //assert(x == 2 * y);
    }
     }
}
