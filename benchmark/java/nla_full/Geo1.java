public class Geo1 {
    public static void vtrace1(int x, int y, int z, int k){}
    public static void vtrace2(int x, int y, int z, int k){}
    public static void main (String[] args) {}


    public static int mainQ(int z, int k){
	//if too large then might cause overflow
	assert(z>=0);
	assert(z<=10);
	assert(k > 0);
	assert(k<=10); 
     
	int x = 1; int y = z; int c = 1;

	while (true){
	    //assert(x*z - x - y + 1 == 0);
	    vtrace1(x, y, z, k);
	    if(!(c < k)) break;
	  
	    c = c + 1;
	    x = x*z + 1;
	    y = y*z;

	}

	x = x *(z - 1);

	//assert(x - y + 1 == 0)
	vtrace2(x, y, z, k);
	return x;
    }
}
