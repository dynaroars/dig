public class POPL09_Fig4_2 {
    public static void vtrace1(int n, int m, int a, int b, int tCtr){}
    public static void main (String[] args) {}
    public static int mainQ(int a, int b, int n, int m){
	int x = a;
	int y = b;

	int tCtr = 0;
	while(x < n){
	    while(y < m){
		y = y + 1;
		tCtr++;
	    }
	    x = x + 1;
	    tCtr++;
	}
	vtrace1(n, m, a, b, tCtr);
	//   l17: -t <= 0, m*n*t + (n*n)*t - m*(t*t) - 2*n*(t*t) + (t*t*t) - m*t*a - 2*n*t*a + 2*(t*t)*a + t*(a*a) - n*t*b + (t*t)*b + t*a*b == 0
	return 0;
    }

}

