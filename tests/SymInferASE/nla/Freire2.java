public class Freire2 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]));
     }

     public static int mainQ(int a){
	  double x,s;
	  int r;
	  x = (double)a;
	  r = 1;
	  s = 3.25;
     
	  while (true){
	       //%%%traces: int a, double x, int r, double s
	       if(!(x-s > 0.0)) break;
	  
	       //assert(((int)(4*r*r*r - 6*r*r + 3*r) + (int)(4*x - 4*a)) == 1); 
	       //assert((int)(4*s) -12*r*r == 1); 
	  
	       x = x - s;
	       s = s + 6 * r + 3;
	       r = r + 1;
	  }
     
	  return r;
     }
}
