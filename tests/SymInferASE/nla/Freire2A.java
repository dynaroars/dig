public class Freire2A {

     public static void main (String[] args) {
	  mainQ(Double.parseDouble(args[0]));
     }

     public static int mainQ(double a){
	  double b,t;
	  int r;
	  b = a;
	  r = 1;
	  t = 3.0;
     
	  while (true){
	       //%%%traces: double a, double b, double t, int r 
	       if(!(b-t > 0.0)) break;
	  
	       //attert(((int)(4*r*r*r - 6*r*r + 3*r) + (int)(4*b - 4*a)) == 1); 
	       //attert((int)(4*t) -12*r*r == 1); 
	  
	       b = b - t;
	       t = t + 6 * r + 3;
	       r = r + 1;
	  }
     
	  return r;
     }
}
