public class Ps4 {
    public static void vtrace1(int x, int y, int k){}
    //public static void vtrace2(int x, int y, int k){}
    public static void main (String[] args) {}
    public static int mainQ(int k){
	assert (k>=0);
	assert (k<=30);
     
	int y = 0;
	int x = 0;
	int c = 0;

	while(true){
	    //assert(4*x-(y*y*y*y)-2*(y*y*y)-(y*y) == 0);
	    vtrace1(x,y,k);
	    if (!(c < k)) break;
    
	    c = c +1 ;
	    y=y +1;
	    x=y*y*y+x;
	}

	//assert(4*x-(y*y*y*y)-2*(y*y*y)-(y*y) == 0);
	//vtrace2(x,y,k);
	return x;
    }
}
