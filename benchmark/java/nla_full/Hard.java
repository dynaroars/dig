/* hardware integer division program, by Manna
returns q==A//B
*/


public class Hard {

    public static void vtrace1(int A, int B, int r, int d, int p, int q){}
    public static void vtrace2(int A, int B, int r, int d, int p, int q){}
    public static void vtrace3(int A, int B, int r, int d, int q){}
    
    public static void main (String[] args) {}

    public static int mainQ(int A, int B){

	assert(B >= 1);

	int r,d,p,q;

	r=A;
	d=B;
	p=1;
	q=0;

	while(true){
	    vtrace1(A, B, r, d, p, q);
	    if (!(r >= d)) break;
	    // assert(A >= 0 && B > 0);
	    // assert(q == 0 && r == A && d == B*p);
	    d = 2 * d;
	    p  = 2 * p;
	}

	while(true){
	    // assert(A == q*B+r);
	    // assert(d==B*p);
	    vtrace2(A, B, r, d, p, q);
	    if (!(p!=1)) break;
    
	    d = d / 2;
	    p = p / 2;
	    if(r >= d){
		r = r - d;
		q = q + p;
	    }
	}

	// assert(d*q - A + r == 0);
	// assert(B == d);
	//p guaranteed to be 1
	vtrace3(A, B, r, d, q); 
	// r == A % B
	// q == A / B
	return q;
    }


}
