public class POPL09_Fig4_1 {
    public static void vtrace_post(int n, int m, int tCtr){}
    public static void main (String[] args) {}

    public static int mainQ(int n, int m){
	assert(m >= 0); 
	int x = 0;
	int y = 0;
	int tCtr = 0;
	while(x < n){
	    if(y < m){
		y = y + 1;
	    }
	    else{
		x = x + 1;
	    }
	    tCtr++;
	}
	vtrace_post(n, m, tCtr);
	//dig2:n - t <= 0, -t <= 0    nothing useful ??
	//NOTE: should we expect t = something here ? 
	return 0;
    }
}

