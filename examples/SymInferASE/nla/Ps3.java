public class Ps3 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]));
     }

     public static int mainQ(int k){
	  assert (k>=0);
	  assert (k<=30);
     
	  int y = 0;
	  int x = 0;
	  int c = 0;


	  while(true){
	       //assert(6*x-2*y*y*y-3*y*y-y == 0);	  
	       //%%%traces: int x, int y, int k

	       if (!(c < k)) break;    
	       c = c +1 ;
	       y=y +1;
	       x=y*y+x;
	  }
	  return x;
     }
}
