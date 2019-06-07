public class Ps3 {
    public static void vtrace1(int x, int y, int k){}
    public static void vtrace2(int x, int y, int k){}
    public static void main (String[] args) {}
    public static int mainQ(int k){
	assert (k<=30);
     
	int y = 0;
	int x = 0;
	int c = 0;
	while(true){
	    //assert(6*x-2*y*y*y-3*y*y-y == 0);	  
	    vtrace1(x, y, k);
	    if (!(c < k)) break;    
	    c = c +1 ;
	    y=y +1;
	    x=y*y+x;
	}
	
	//assert(6*x-2*y*y*y-3*y*y-y == 0);	  
	vtrace2(x,y,k);
	return x;
    }
}
