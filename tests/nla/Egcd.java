public class Egcd {
    public static void vtrace1(int x, int y, int a, int b, int p, int q, int r, int s){}
    public static void vtrace2(int x, int y, int a, int b, int p, int q, int r, int s){}
    public static void main (String[] args) {}

    public static int mainQ(int x, int y){
	/* extended Euclid's algorithm */
	assert(x >= 1);
	assert(y >= 1);
	int a,b,p,q,r,s;
    
	a=x;
	b=y;
	p=1;
	q=0;
	r=0;
	s=1;

	while(true){
	    //assert(1 == p*s - r*q);
	    //assert(a == y*r + x*p);
	    //assert(b == x*q + y*s);
	  
	    //%%%traces: int x, int y, int a, int b, int p, int q, int r, int s
	    vtrace1(x,y,a,b,p,q,r,s);
	       
	    if(!(a!=b)) break;
	  
	    if (a>b) {
		a = a-b; 
		p = p-q; 
		r = r-s;
	    }
	    else {
		b = b-a; 
		q = q-p; 
		s = s-r;}
	}
	vtrace2(x,y,a,b,p,q,r,s);
	return a;
    }


}
