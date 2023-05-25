public class Freire1 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]));
     }

     public static int mainQ(int a) {
	  double x = ((double)a)/2.0;
	  int r = 0;


	  while(true){
	       //assert((double)a == 2*x + r*r - r); 
	       //%%%traces: int a, double x, int r
	  
	       if (!(x>r)) break;
	       x = x - r;
	       r = r + 1;
	  }

	  //assert(r==(int)round(sqrt(a)));
	  return r;	  

     }
}
