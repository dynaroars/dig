public class Geo3 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]));
     }

     public static int mainQ(int z, int a, int k){
	  //if too large then might cause overflow
	  assert(z>=0);
	  assert(z<=10);
	  assert(k > 0);
	  assert(k<=10); 

	  int x = a; int y = 1;  int c = 1;

	  while (true){
	       //assert(z*x-x+a-a*z*y == 0);
	       //%%%traces: int x, int y, int z, int a, int k

	       if (!(c < k)) break;
	       c = c + 1;
	       x = x*z + a;
	       y = y*z;

	  }
	  return x;
     }

}
