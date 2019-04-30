public class Freire2 {
     public static void vtrace1(float a, float x, int r, float s){}
     public static void main (String[] args) {}

     public static int mainQ(float a){
	  float x,s;
	  int r;
	  x = a;
	  r = 1;
	  s = 3.25f;
     
	  while (true){
	       vtrace1(a, x, r, s);
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
