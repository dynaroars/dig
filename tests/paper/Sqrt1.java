public class Sqrt1 {
    public static void vtrace1(int a, int n, int t, int s){}
    // public static void vtrace2(int a, int n, int t, int s){}    
    public static void main (String[] args) {}

    public static int mainQ(int n){
	//for a to be sqrt of n,  needs to assume that n >= 0
	assert(n >= 0);

	int a,s,t;
	a=0;
	s=1;
	t=1;

	int ctr = 0;
	while(true){
	    //assert(t == 2*a + 1);
	    //assert(s == (a + 1)*(a + 1));
	    //assert(4s == t*t + 2*t + 1);
	    vtrace1(a, n, t, s);
	    if(!(s <= n)) break;
	    a=a+1;
	    t=t+2;
	    s=s+t;
	}
	// vtrace2(a, n, t, s);
	/*
	  2*a - t + 1 == 0
	  (t*t) - 4*s + 2*t + 1 == 0
	*/
	return a;
     
    }
}
