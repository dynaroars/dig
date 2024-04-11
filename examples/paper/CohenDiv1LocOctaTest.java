public class CohenDiv1LocOctaTest {
    public static void vtrace1(int q, int r, int a, int b, int x, int y, int m, int n, int p, int s){}
    public static void main (String[] args) {}

    public static int mainQ(int x, int y) {
	assert(x >= 1);
	assert(y >= 1);

	int q=0;
	int r=x;
	int a=0;
	int b=0;
	int m = 2*q;
	int n= 2*x;
	int p = 2*a;
	int s = 2*r;
	  
	while(true) {
	    //assert(q*y + r == x);
	    //assert(a*y == b);
	    
	    vtrace1(q,r,a,b,x,y,m,n,p,s);
	    
	    if(!(r>=y)) break;
	    a=1;
	    b=y;
	    p = 2*a;

	    while (true) {
		//assert(q*y + r == x);
		//assert(a*y == b);

		if(!(r >= 2*b)) break;

		a = 2*a;
		b = 2*b;
		p = 2*a;
	    }
	    r=r-b;
	    q=q+a;
	    s = 2*r;
	    m = 2*q;
	}
	return q;
    }
}
