public class POPL09_Fig4_1 {
    public static void vtrace_post(int n, int m, int tCtr) {
    }


    public static int mainQ(int n, int m) {
	assert (m >= 0);
	int x = 0;
	int y = 0;
	int tCtr = 0;
	while (x < n) {
	    if (y < m) {
		y = y + 1;
	    } else {
		x = x + 1;
	    }
	    tCtr++;
	}
	vtrace_post(n, m, tCtr);
	/*
	 * SymInfer Results
	 * 1. m*tCtr + n*tCtr - tCtr^2 == 0 
	 * 2. -m <= 0 
	 * 3. -tCtr <= 0 
	 * 4. n - tCtr <= 0
	 */
	return 0;
    }
}
