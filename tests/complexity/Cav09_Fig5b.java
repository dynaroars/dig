public class Cav09_Fig5b {
    public static void vtrace_post(int a, int n, int y, int x, int tCtr){}
    public static void main (String[] args) {}

    public static int mainQ(int a, int n){
	int x = 0;
	int y = a;
	int tCtr = 0;
	while(x < n){
	    y++;
	    x = x + y;
	    tCtr++;
	  
	}

	//%%%traces: int a, int n, int y, int x, int t
	//dig2:  (y*y) - (a*a) - 2*x + y - a == 0, -x <= 0, n - x <= 0, t - y + a == 0, -y + a <= 0
	vtrace_post(a, n, y, x, tCtr);
	
	return 0;
    }

}

