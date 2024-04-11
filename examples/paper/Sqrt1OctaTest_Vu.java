public class Sqrt1OctaTest_Vu {
    //public static void vtrace1(int p, int t){}
    public static void vtrace1(int a, int n, int t, int s, int m, int k, int p){}
    // public static void vtrace2(int a, int n, int t, int s){}    
    public static void main (String[] args) {}

    public static int mainQ(int n){
	//for a to be sqrt of n,  needs to assume that n >= 0
	assert(n >= 0);

	int a,s,t,m,k,p, e1;
	a=0;
	s=1;
	t=1;
	m=2*a;
	k=2*t;
	p=2*n;
	//e1 = -p + t;

	while(true){
	    //assert(t == 2*a + 1);
	    //assert(s == (a + 1)*(a + 1));
	    //assert(4s == t*t + 2*t + 1);
	    vtrace1(a, n, t, s, m, k, p);
	    //vtrace1(p, t);
	    if(!(s <= n)) break;
	    //e1 = -p + t;
	    a=a+1;
	    t=t+2;
	    s=s+t;
	    m=2*a;
	    k=2*t;
	}
	// vtrace2(a, n, t, s);
	/*
	  2*a - t + 1 == 0
	  (t*t) - 4*s + 2*t + 1 == 0
	*/
	return a;
     
    }
}

