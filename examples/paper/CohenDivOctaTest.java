public class CohenDivOctaTest {
    public static void vtrace1(int q, int r, int a, int b, int x, int y, int m, int k, int p, int t, int s, int l){}
    public static void vtrace2(int x, int y, int q, int r, int k, int l, int t, int m){}

    public static void main (String[] args) {}
    public static int mainQ(int x, int y) {
	assert(x >= 0);
	assert(y >= 1);

	int q=0;
	int r=x;
	int a=0;
	int b=0;
	int m = 2*r;
	int k = 2*x;
	int p = 2*b;
	int t = 2*q;
	int s = 2*a;
	int l = 2*y;

	  
	while(true) {
	    if(!(r>=y)) break;
	    a=1;
	    b=y;
	    s = 2*a;
	    p = 2*b;

	    while (true) {
		vtrace1(q,r,a,b,x,y,m,k,p,t,s,l);
		if(!(r >= 2*b)) break;

		a = 2*a;
		b = 2*b;
		s = 2*a;
                p = 2*b;
	    }
	    r=r-b;
	    q=q+a;
	    m = 2*r;
	    t = 2*q;
	}

	vtrace2(x,y,q,r,k,l,t,m);
	return q;
    }
}
