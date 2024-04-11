//swap: a += (b - (b = a));
public class OddEven6 {
    public static void vtrace1(int x0, int x1, int x2,
			       int x3, int x4, int x5,
			       int t0, int t1, int t2,
			       int t3, int t4, int t5){}

    public static void main (String[] args) {}
     
    public static void mainQ_cohendiv(int t0, int t1, int t2,
				      int t3, int t4, int t5) {
	int x0 = t0;
	int x1 = t1;
	int x2 = t2;
	int x3 = t3;
	int x4 = t4;
	int x5 = t5;
	
	if (x0 > x1){
	    x0 += (x1 - (x1 = x0));
	}
	
	if (x2 > x3){
	    x2 += (x3 - (x3 = x2));
	}

	if (x4 > x5){
	    x4 += (x5 - (x5 = x4));
	}

	if (x1 > x2){
	    x1 += (x2 - (x2 = x1));
	}
	if (x3 > x4){
	    x3 += (x4 - (x4 = x3));
	}
	
	if (x0 > x1){
	    x0 += (x1 - (x1 = x0));
	}
	
	if (x2 > x3){
	    x2 += (x3 - (x3 = x2));
	}

	if (x4 > x5){
	    x4 += (x5 - (x5 = x4));
	}

	if (x1 > x2){
	    x1 += (x2 - (x2 = x1));
	}
	if (x3 > x4){
	    x3 += (x4 - (x4 = x3));
	}		
	
	assert(x0 <=x1 && x1 <= x2 && x2 <= x3 && x3 <= x4 && x4 <= x5);
	vtrace1(x0,x1,x2,x3,x4,x5,t0,t1,t2,t3,t4,t5);
    }
}
