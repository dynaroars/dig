//swap: a += (b - (b = a));
public class OddEven2 {
    public static void vtrace1(int x0, int x1, int t0, int t1){}

    public static void main (String[] args) {}
     
    public static void mainQ(int t0, int t1) {
	int x0 = t0;
	int x1 = t1;
	if (x0 >= x1){
	    x0 += (x1 - (x1 = x0));
	}

	assert(x1 >= x0);
	vtrace1(x0,x1,t0,t1);
    }
}
