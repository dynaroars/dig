public class Sqrt1NonLin {
    public static void vtrace1(int a, int n, int t, int s, int a2, int n2, int t2, int s2, int an, int at, int m, int nt, int ns, int ts){}
    // public static void vtrace2(int a, int n, int t, int s){}    
    public static void main (String[] args) {}

    public static int mainQ(int n){
	//for a to be sqrt of n,  needs to assume that n >= 0
	assert(n >= 0);

	int a,s,t;
	int a2, n2, t2, s2, an, at, m, nt, ns, ts;
	a=0;
	s=1;
	t=1;
	a2 = a*a;
	n2 = n*n;
	t2 = t*t;
	s2 = s*s;
	an = a*n;
	at = a*t;
	m = a*s;
	nt = n*t;
	ns = n*s;
	ts = t*s;

	int ctr = 0;
	while(true){
	    //assert(t == 2*a + 1);
	    //assert(s == (a + 1)*(a + 1));
	    //assert(4s == t*t + 2*t + 1);
	    vtrace1(a, n, t, s, a2, n2, t2, s2, an, at, m, nt, ns, ts);
	    if(!(s <= n)) break;
	    a=a+1;
	    t=t+2;
	    s=s+t;
	    a2 = a*a;
	    t2 = t*t;
	    s2 = s*s;
	    an = a*n;
	    at = a*t;
	    m = a*s;
	    nt = n*t;
	    ns = n*s;
	    ts = t*s;

	}
	// vtrace2(a, n, t, s);
	/*
	  2*a - t + 1 == 0
	  (t*t) - 4*s + 2*t + 1 == 0
	*/
	return a;
     
    }
}
