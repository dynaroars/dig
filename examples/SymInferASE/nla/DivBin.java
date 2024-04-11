public class DivBin {

     public static void main (String[] args) {
	  mainQ_divbin(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static int mainQ_divbin(int A, int B) {
	  assert(A > 0 && B > 0 && A >= B);
 
	  int q = 0;
	  int r = A;
	  int b = B;

	  while(true){
	       //%%%traces: int A, int B, int q, int r, int b
	       if (!(r >= b)) break;
	       b=2*b;
	  }

	  while(true){
	       //assert(A == q*b + r && r >= 0);
	       //%%%traces: int A, int B, int q, int r, int b
	       if (!(b!=B)) break;
	  
	       q = 2*q;
	       b = b/2;
	       if (r >= b) {
		    q = q + 1;
		    r = r - b;
	       }
	  }
	  return 0;	  

     }
}
