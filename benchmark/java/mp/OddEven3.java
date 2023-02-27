//swap: a += (b - (b = a));
public class OddEven3 {
    public static void vtrace1(int y0, int y1, int y2, int x0, int x1, int x2){}

    public static void main (String[] args) {}
     
    public static void mainQ_cohendiv(int x0, int x1, int x2) {
	int y0 = x0;
	int y1 = x1;
	int y2 = x2;
	
	if (y0 > y1){
	    y0 += (y1 - (y1 = y0));
	}

	if (y1 > y2){
	    y1 += (y2 - (y2 = y1));
	}

	if (y0 > y1){
	    y0 += (y1 - (y1 = y0));
	}

	if (y1 > y2){
	    y1 += (y2 - (y2 = y1));
	}
	
	//assert(y0 <=y1 && y1 <= y2);
	vtrace1(y0,y1,y2,x0,x1,x2);
    }
}
