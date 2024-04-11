//swap: a += (b - (b = a));
public class OddEven4 {
    public static void vtrace1(int y0, int y1, int y2, int y3,
			       int x0, int x1, int x2, int x3){}

    public static void main (String[] args) {}
     
    public static void mainQ_cohendiv(int x0, int x1, int x2, int x3) {
	int y0 = x0;
	int y1 = x1;
	int y2 = x2;
	int y3 = x3;
	
	if (y0 > y1){
	    y0 += (y1 - (y1 = y0));
	}
	
	if (y2 > y3){
	    y2 += (y3 - (y3 = y2));
	}
	
	if (y1 > y2){
	    y1 += (y2 - (y2 = y1));
	}

	if (y0 > y1){
	    y0 += (y1 - (y1 = y0));
	}
	
	if (y2 > y3){
	    y2 += (y3 - (y3 = y2));
	}
	
	if (y1 > y2){
	    y1 += (y2 - (y2 = y1));
	}
	
	
	//assert(y0 <=y1 && y1 <= y2 && y2 <= y3);
	vtrace1(y0,y1,y2,y3,x0,x1,x2,x3);
    }
}
