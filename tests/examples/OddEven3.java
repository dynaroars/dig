//swap: a += (b - (b = a));
public class OddEven3 {
    public static void vtrace1(int x0, int x1, int x2, int t0, int t1, int t2){}

    public static void main (String[] args) {}
     
    public static void mainQ_cohendiv(int t0, int t1, int t2) {
	int x0 = t0;
	int x1 = t1;
	int x2 = t2;
	
	if (x0 > x1){
	    x0 += (x1 - (x1 = x0));
	}

	if (x1 > x2){
	    x1 += (x2 - (x2 = x1));
	}

	if (x0 > x1){
	    x0 += (x1 - (x1 = x0));
	}

	if (x1 > x2){
	    x1 += (x2 - (x2 = x1));
	}
	
	assert(x0 <=x1 && x1 <= x2);
	vtrace1(x0,x1,x2,t0,t1,t2);
    }
}
