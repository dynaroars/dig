public class POPL09_Fig2_2 {
    public static void vtrace_post(int n, int a, int b, int tCtr){}
    public static void main (String[] args) {}
    public static int mainQ(int a, int b, int n){
	int x = a;
	int y = b;
	int tCtr = 0;
	while(x < n){
	    if(y > x){
		x++;
	    }
	    else{
		y++;
	    }
	    tCtr++;
	}
	vtrace_post(n, a, b, tCtr);

	//dig2: 2*n^2*t - 3*n*t^2 + t^3 - 3*n*t*a + 2*t^2*a + t*a^2 - n*t*b + t^2*b + t*a*b == 0
	//solve for t got t == 2*n - a - b, t == n - a, t == 0
	//NOTE: *** are these results correct, better, etc than the given bound of Max(0, n-a) + Max(0, n-b)
	//Timos: Look at comment in Fig2_1.c. Same reasoning applies here.
	return 0;
    }
}

