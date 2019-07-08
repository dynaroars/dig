public class POPL09_Fig2_2 {
    public static void vtrace1(int n, int x0, int z0, int tCtr){}
    public static void main (String[] args) {}
    public static int mainQ(int x0, int z0, int n){
	int x = x0;
	int z = z0;
	int tCtr = 0;
	while(x < n){
	    if(z > x){
		x++;
	    }
	    else{
		z++;
	    }
	    tCtr++;
	}
	vtrace1(n, x0, z0, tCtr);

	//dig2: 2*n^2*t - 3*n*t^2 + t^3 - 3*n*t*x0 + 2*t^2*x0 + t*x0^2 - n*t*z0 + t^2*z0 + t*x0*z0 == 0
	//solve for t got t == 2*n - x0 - z0, t == n - x0, t == 0
	//NOTE: *** are these results correct, better, etc than the given bound of Max(0, n-x0) + Max(0, n-z0)
	//Timos: Look at comment in Fig2_1.c. Same reasoning applies here.
	return 0;
    }
}

