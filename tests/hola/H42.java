public class H42 {

    public static void vtrace(int a, int y, int x){}
     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static void mainQ(int flag, int u1){
	  assert(u1 > 0);
	  int x = 1;
	  int y = 1;
	  int a = 0;

	  if (flag != 0)
	       a = 0;
	  else
	       a = 1;

	  int i1 = 0;
	  while (i1 < u1) {
	       i1++;

	       if (flag != 0) {
		    a = x + y;
		    x++;
	       } else {
		    a = x + y + 1;
		    y++;
	       }
	       if (a % 2 == 1)
		    y++;
	       else
		    x++;
	  }
	  // x==y

	  if (flag != 0) a++;
	  //%%%traces: int a, int y, int x
    vtrace(a, y, x);
	  //assert(a % 2 == 1);
     }
}
