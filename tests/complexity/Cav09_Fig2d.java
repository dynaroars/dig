public class Cav09_Fig2d {
    public static void vtrace_post(int n, int m, int tCtr){}
    public static void main (String[] args) {}
    public static int mainQ(int n, int m){
	//these assertions are based on gulwani pldi fig 4_3
	//(same as cav fig 2a).
	assert (m > 0);
	assert (n > m);
     
	int x = 0;
	int y = 0;
	int tCtr = 0;
	while(x < n){
	    while (y < m){
		tCtr++;
		y++;
	    }
	    y=0;
	    x++;
	    //TVN: why not add a tCtr++ here?
	}
	vtrace_post(n, m, tCtr);
	//%%%traces: int n, int m, int t
	//dig2: -m <= -1, m*n - t == 0, m - n <= -1
	return 0;
    }


}

