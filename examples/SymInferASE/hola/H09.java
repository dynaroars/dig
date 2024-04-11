public class H09 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]),Integer.parseInt(args[3]),Integer.parseInt(args[4]), Integer.parseInt(args[5]), Integer.parseInt(args[6]));
     }

     public static void mainQ(int j, int n, int t, int pvlen, int u1, int u2, int u3) {

	  int k = 0;
	  int i = 0;
	  int i1 = 0;
	  int i2 = 0;
	  int i3 = 0;

	  //  pkt = pktq->tqh_first;
	  while (i1 < u1) {
	       i1 = i1 + 1;
	       i = i + 1;
	  }

	  if (i > pvlen) {
	       pvlen = i;
	  } else {
	  }
	  i = 0;

	  while (i2 < u2) {
	       i2 = i2 + 1;
	       t = i;
	       i = i + 1;
	       k = k + 1;
	  }

	  while (i3 < u3) {
	       i3 = i3 + 1;
	  }

	  j = 0;
	  n = i;

	  //%%%traces: int k
	  //assert(k >= 0);
	  k = k - 1;
	  i = i - 1;
	  j = j + 1;
	  while (j < n) {
	       //%%%traces: int k
	       //assert(k >= 0);
	       k = k - 1;
	       i = i - 1;
	       j = j + 1;
	  }
	  //PRINT_VARS();
	  //PRINT_BAR(4);
     }
}
