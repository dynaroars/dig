public class Cav09_Fig1d {
    public static void vtrace_post(int m, int tCtr){}
    public static void main (String[] args) {}
    public static int mainQ(int m){
	int x = 0;
	int y = 0;
	int tCtr = 0;
	while(x < 100 && y < m){
	    y++;
	    tCtr++;
	}
	while(x < 100 && y >= m){
	    x++;
	    tCtr++;
	}
	vtrace_post(m, tCtr);
	//%%%traces: int m, int t
	//dig2: m*t - (t*t) - 100*m + 200*t - 10000 == 0
	//solve for t: t == m + 100, t == 100
	return 0;	  
    }
}

