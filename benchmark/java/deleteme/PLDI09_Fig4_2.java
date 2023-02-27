public class PLDI09_Fig4_2 {
    public static void vtrace_post(int n, int m, int tCtr, int x, int y){}
    public static void main (String[] args) {}
    public static int mainQ(int n, int m){
	assert (n > 0);
	assert (m > 0);
	int x = n;
	int y = 0;
	int tCtr = 0;
	while(x > 0){
	    if (y < m) {
		y++;
		x--;
	    }else{
		y=0;
	    }
	    tCtr++;
	}

     
	vtrace_post(n, m, tCtr, x, y);
	//dig2: l23: -t + y <= 0, -m + y <= 0, x == 0, m*n - m*t + n - y == 0, x - y <= -1
	//Note: cannot find relationship among t and m,n  (annotated n+n/m)
	return 0;
    }

}

