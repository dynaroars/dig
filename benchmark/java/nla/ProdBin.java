public class ProdBin {
    public static void vtrace1(int a, int b, int x, int y, int z){}
    //public static void vtrace2(int a, int b, int x, int z){}
    public static void main (String[] args) {}
    public static int mainQ(int a, int b){
	assert(a >= 0);	/* SPF/Z3 has some prob without this*/
	assert(b >= 0);

	int x,y,z;
	x = a;
	y = b;
	z = 0;
	
	while(true) { 
	    //assert(z+x*y==a*b);
	    vtrace1(a, b, x, y, z);
	    
	    if(!(y != 0)) break;
	  
	    if (y % 2 == 1){
		z = z+x;
		y = y-1;
	    }
	    x = 2*x;
	    y = y/2;

	}
	
	//assert(z == a*b);
	//do not consider y as it will be 0
	//vtrace2(a, b, x, z);
	return z; 
    }
}
