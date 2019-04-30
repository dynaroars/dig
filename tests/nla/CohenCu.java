public class CohenCu {

     public static void vtrace1(int a, int n, int x, int y, int z){}
     public static void main (String[] args) {
     }

     public static int mainQ_cohencu(int a) {
	  int n,x,y,z;
	  n=0; x=0; y=1; z=6;
	  
	  while(true){
	       //assert(z == 6*n + 6);
	       //assert(y == 3*n*n + 3*n + 1);
	       //assert(x == n*n*n);
	       //%%%traces: 
	       vtrace1(a,n,x,y,z);
	       if(!(n<=a)) break;
      
	       n=n+1;
	       x=x+y;
	       y=y+z;
	       z=z+6;
	  }
	  return x;
     }
}
