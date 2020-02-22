public class H40 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]));
     }

     public static void mainQ(int flag, int u1, int u2) { 
	  assert(u1 > 0 && u2 > 0);

	  int j = 1;
	  int i = 0;
	  if (flag != 0) {
	       i = 0;
	  } else {
	       i = 1;
	  }

	  int i1 = 0;
	  while (i1 < u1) {
	       i1++;
	       i += 2;
	       if (i % 2 == 0) {
		    j += 2;
	       } else
		    j++;
	  }

	  int a = 0;
	  int b = 0;

	  int i2 = 0;
	  while (i2 < u2) {
	       i2++;
	       a++;
	       b += (j - i);
	  }

	  //%%%traces: int a, int b, int i, int j, int u1, int u2, int flag
	  //if (flag != 0) assert(a == //b);
				

     }
}  
