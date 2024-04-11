public class CohenDivPost {
    public static void vtrace1(int q, int r, int a, int b, int x, int y){}
    public static void main (String[] args) {}

    public static int mainQ(int x, int y) {
	assert(x >= 1);
	assert(y >= 1);

	int q=0;
	int r=x;
	int a=0;
	int b=0;
	  
	while(true) {
	    //assert(q*y + r == x);
	    //assert(a*y == b);	    
	    
	    if(!(r>=y)) break;
	    a=1;
	    b=y;

	    while (true) {
		//assert(q*y + r == x);
		//assert(a*y == b);

		if(!(r >= 2*b)) break;

		a = 2*a;
		b = 2*b;
	    }
	    r=r-b;
	    q=q+a;
	}
	vtrace1(q,r,a,b,x,y);	
	return q;
    }
}
