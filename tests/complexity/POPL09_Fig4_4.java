public class POPL09_Fig4_4 {
    public static void vtrace1(int n, int m, int tCtr){}    
    public static void main (String[] args) {}
    public static int mainQ(int n, int m){
	assert(m >= 0);
	assert(n >= 0);
	int x = 0;
	int y = 0;
	int tCtr = 0;
	while(x < n){
	    y=0;
	    x++;
	    while(y < m){
		y++;
		tCtr++;
	    }
	    tCtr++;
	}
	vtrace1(n, m, tCtr);
	//dig2: t>= 0
	//NOTE: *** why didn't I get anything useful here ?  should t = some function of n, m ?
	// Again, there is a t++ missing for the outer loop. I ran the corrected version on DIG1 and got m*n + n - t == 0 which looks correct.
	return 0;
    }

}

