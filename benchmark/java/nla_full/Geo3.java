public class Geo3 {
    public static void vtrace1(int x, int y, int z, int a, int k){}
    public static void vtrace2(int x, int y, int z, int a, int k){}
    public static void main (String[] args) {}
    public static int mainQ(int z, int a, int k){
	//if too large then might cause overflow
	assert(z>=0);
	assert(z<=10);
	assert(k > 0);
	assert(k<=10); 

	int x = a; int y = 1;  int c = 1;

	while (true){
	    //assert(z*x-x+a-a*z*y == 0);
	    vtrace1(x, y, z, a, k);
	    if (!(c < k)) break;
	    c = c + 1;
	    x = x*z + a;
	    y = y*z;

	}
	//vtrace2(x, y, z, a, k);
	return x;
    }

}
