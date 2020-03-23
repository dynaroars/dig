public class Ps5 {
    public static void vtrace1(int x, int y, int k){}
    public static void vtrace2(int x, int y, int k){}
    public static void main (String[] args) {}
    public static int mainQ(int k){
	assert (k>=0);
	assert (k <= 30); //if too large then will cause overflow
	int y = 0;
	int x = 0;
	int c = 0;

	while(true){
	    //assert(6*y*y*y*y*y + 15*y*y*y*y+ 10*y*y*y - 30*x - y == 0);
	    vtrace1(x, y, k);
	    if (!(c < k)) break;
	    c = c +1 ;
	    y=y +1;
	    x=y*y*y*y+x;
	}

	//assert(6*y*y*y*y*y + 15*y*y*y*y+ 10*y*y*y - 30*x - y == 0);
	//assert(k*y == y*y);
	vtrace2(x, y, k);
	return x;
    }
}
