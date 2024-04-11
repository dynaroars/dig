//swap: a += (b - (b = a));
public class OddEven8 {
    public static void vtrace1(int x0, int x1, int x2,
			       int x3, int x4, int x5, int x6, int x7,
			       int t0, int t1, int t2,
			       int t3, int t4, int t5, int t6, int t7){}

    public static void main (String[] args) {}
     
    public static void mainQ_cohendiv(int t0, int t1, int t2, int t3, 
				      int t4, int t5, int t6, int t7) {
	int x0 = t0;
	int x1 = t1;
	int x2 = t2;
	int x3 = t3;
	int x4 = t4;
	int x5 = t5;
	int x6 = t6;
	int x7 = t7;
	
	if (x0 > x1){
	    x0 += (x1 - (x1 = x0));
	}
	if (x2 > x3){
	    x2 += (x3 - (x3 = x2));
	}
	if (x4 > x5){
	    x4 += (x5 - (x5 = x4));
	}
	if (x6 > x7){
	    x6 += (x7 - (x7 = x6));
	}
	if (x1 > x2){
	    x1 += (x2 - (x2 = x1));
	}
	if (x3 > x4){
	    x3 += (x4 - (x4 = x3));
	}
	if (x5 > x6){
	    x5 += (x6 - (x6 = x5));
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
	if (x6 > x7){
	    x6 += (x7 - (x7 = x6));
	}
	if (x1 > x2){
	    x1 += (x2 - (x2 = x1));
	}
	if (x3 > x4){
	    x3 += (x4 - (x4 = x3));
	}
	if (x5 > x6){
	    x5 += (x6 - (x6 = x5));
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
	if (x6 > x7){
	    x6 += (x7 - (x7 = x6));
	}
	if (x1 > x2){
	    x1 += (x2 - (x2 = x1));
	}
	if (x3 > x4){
	    x3 += (x4 - (x4 = x3));
	}
	if (x5 > x6){
	    x5 += (x6 - (x6 = x5));
	}
	assert(x0 <=x1 && x1 <= x2 && x2 <= x3 &&
	       x3 <= x4 && x4 <= x5 && x5 <= x6 && x6 <= x7);
	vtrace1(x0,x1,x2,x3,x4,x5,x6,x7,t0,t1,t2,t3,t4,t5,t6,t7);
    }
}
