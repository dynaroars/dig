public class POPL09_Fig4_2 {
    public static void vtrace1(int n, int m, int x0, int y0, int t){}
    public static void main (String[] args) {}
    public static int mainQ(int x0, int y0, int n, int m){
	int x = x0;
	int y = y0;

	int t = 0;
	while(x < n){
	    while(y < m){
		y = y + 1;
		t++;
	    }
	    x = x + 1;
	    t++;
	}
	vtrace1(n, m, x0, y0, t);
	//   l17: -t <= 0, m*n*t + (n*n)*t - m*(t*t) - 2*n*(t*t) + (t*t*t) - m*t*x0 - 2*n*t*x0 + 2*(t*t)*x0 + t*(x0*x0) - n*t*y0 + (t*t)*y0 + t*x0*y0 == 0
	return 0;
    }

}

