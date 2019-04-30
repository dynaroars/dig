public class POPL09_Fig4_1 {
    public static void vtrace1(int n, int m, int t){}
    public static void main (String[] args) {}

    public static int mainQ(int n, int m){
	assert(m >= 0); 
	int x = 0;
	int y = 0;
	int t = 0;
	while(x < n){
	    if(y < m){
		y = y + 1;
	    }
	    else{
		x = x + 1;
	    }
	    t++;
	}
	vtrace1(n, m, t);
	//dig2:n - t <= 0, -t <= 0    nothing useful ??
	//NOTE: should we expect t = something here ? 
	return 0;
    }
}

