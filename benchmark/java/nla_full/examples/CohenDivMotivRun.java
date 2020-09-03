public class CohenDivMotivRun {
    public static void vtrace1(int q, int r, int a, int b, int x, int y){}
    public static void vtrace2(int x, int y, int q, int r){}

    public static void main (String[] args) {
	int x = Integer.parseInt(args[1]);
	int y = Integer.parseInt(args[2]);
	
	assert(x>=0);
	assert(y >= 1);

	//fake
	assert(x != 0);
	assert(y==1);

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

		vtrace1(q,r,a,b,x,y);
		if(!(r >= 2*b)) break;

		a = 2*a;
		b = 2*b;
	    }
	    r=r-b;
	    q=q+a;
	}
	//assert(q*y + r == x);
	vtrace2(x,y,q,r);
	return q;
    }
}
