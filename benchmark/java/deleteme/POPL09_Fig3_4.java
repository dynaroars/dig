public class POPL09_Fig3_4 {
    public static void vtrace_post(int n, int m, int tCtr){}
    public static void main (String[] args) {}
    public static int mainQ (int n, int m){
	int x = 0;
	int y = 0;
	int tCtr = 0;
	while((x < n || y < m)){
	    if(x < n){
		x++;
		y++;
	    }
	    else if(y < m){
		x++;
		y++;
	    }
	    else{
		assert(false);
		break;
	    }
	    tCtr++;
	}
	vtrace_post(n, m, tCtr);
	//dig2: m*n*t - m*(t*t) - n*(t*t) + (t*t*t) == 0, m - t <= 0, n - t <= 0, -t <= 0
	//solve for t : t == n, t == m, t == 0
	//NOTE: *** are the above correct ? there are 3 exact bounds as indicated for this?
	//Timos: This looks correct to me. A more correct bound would be Min(n,m)
	return 0;
    }

}

