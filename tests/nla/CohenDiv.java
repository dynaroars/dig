public class CohenDiv {
    public static void vtrace1(int q, int r, int a, int b, int x, int y){}
    public static void vtrace2(int x, int y, int q, int r){}

    public static void main (String[] args) {}
     

    public static int mainQ_cohendiv(int x, int y) {
	assert(x>0 && y>0);

	int q=0;
	int r=x;
	int a=0;
	int b=0;
	  
	while(true) {
	    if(!(r>=y)) break;
	    a=1;
	    b=y;

	    while (true) {
		vtrace1(q,r,a,b,x,y);
		if(!(r >= 2*b)) break;

		a = 2*a;
		b = 2*b;
	    }
	    r=r-b;
	    q=q+a;
	}
	vtrace2(x,y,q,r);
	return q;
    }
}
