public class ProdBin {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static int mainQ(int a, int b){
	  assert(a>=0);
	  assert(b>=0);

	  int x,y,z;
	  x = a;
	  y = b;
	  z = 0;

	  while(true) { 
	       //assert(z+x*y==a*b);
	       //%%%traces: int a, int b, int x, int y, int z
	       if(!(y!=0)) break;
	  
	       if (y%2 ==1 ){
		    z = z+x;
		    y = y-1;
	       }
	       x = 2*x;
	       y = y/2;

	  }
	  assert(z == a*b);
	  return z; 

     }
}
