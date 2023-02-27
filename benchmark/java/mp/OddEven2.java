//swap: a += (b - (b = a));
public class OddEven2 {
    public static void vtrace1(int y0, int y1, int x0, int x1){}

    public static void main (String[] args) {}
     
    public static void mainQ(int x0, int x1) {
	int y0 = x0;
	int y1 = x1;
	if (y0 >= y1){
	    y0 += (y1 - (y1 = y0));
	}

	//assert(y0 <= y1);
	vtrace1(y0,y1,x0,x1);
    }
}
