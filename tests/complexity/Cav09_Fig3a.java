public class Cav09_Fig3a {
    public static void vtrace1(int n, int t){}
    public static void main (String[] args) {}
    public static int mainQ(int n){
	int x = 0;
	int y = 0;
	int t = 0;
	while(x < n){
	    y = x;
	    while (y < n){
		t++;
		y++;
	    }
	  
	    x=y+1;
	}

	vtrace1(n, t);
	//%%%traces: int n, int t
	//dig2:  n*t - (t*t) == 0, -t <= 0, n - t <= 0
	return 0;
    }
}
