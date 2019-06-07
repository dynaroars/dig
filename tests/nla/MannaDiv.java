public class MannaDiv {
    public static void vtrace1(int y1, int y2, int y3, int x1, int x2){}
    public static void vtrace2(int y1, int y2, int x1, int x2){}    
    public static void main (String[] args) {}

    public static int mainQ(int x1, int x2){
	assert (x1 >= 0);
	assert (x2 != 0);
     
	int y1, y2, y3;
	y1 = 0;
	y2 = 0;
	y3 = x1;

	while(true) {
	    //assert(y1* x2 + y2 + y3 == x1);
	    vtrace1(y1, y2, y3, x1, x2);
	  
	    if(!(y3 != 0)) break;
	  
	    if (y2 + 1 == x2) {
		y1 = y1 + 1;
		y2 = 0;
		y3 = y3 - 1;
	    }
	    else {
		y2 = y2 + 1;
		y3 = y3 - 1;
	    }
	}
	//assert x2*y1 - x1 + y2 == 0
	//y3 guarantees to be 0
	vtrace2(y1, y2, x1, x2); 
	//assert(y1 == x1 / x2);
	return y1;
    }
}
