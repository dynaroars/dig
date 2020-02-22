public class Geo2 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static int mainQ(int z, int k){
	  //if too large then might cause overflow
	  assert(z>=0);
	  assert(z<=10);
	  assert(k>0);
	  assert(k<=10);
	  int x = 1; int y = 1; int c = 1;

	  while (true){
	       //assert(1+x*z-x-z*y==0);
	       //%%%traces: int x, int y, int z, int k
	       //printf("%d %d %d %d\n", x, y ,z, k);
	  
	       if(!(c < k)) break;
	       c = c + 1;
	       x = x*z + 1;
	       y = y*z;
	  }
	  return x;
     }
}
