public class DivBin {
    public static void vtrace1(int A, int B, int q, int r, int b){}
    public static void vtrace2(int A, int B, int q, int r, int b){}
    public static void vtrace3(int A, int B, int q, int r, int b){}    
	  
    public static void main (String[] args) {	  
    }

    public static int mainQ_divbin(int A, int B) {
	assert(B >= 1);
 
	int q = 0;
	int r = A;
	int b = B;

	while(true){
	    vtrace1(A,B,q,r,b);
	    if (!(r >= b)) break;
	    b=2*b;
	}

	while(true){
	    //assert(A == q*b + r);
	    vtrace2(A,B,q,r,b);
	    if (!(b!=B)) break;
	  
	    q = 2*q;
	    b = b/2;
	    if (r >= b) {
		q = q + 1;
		r = r - b;
	    }
	}
	//_assert(A == q * b + r)
	vtrace3(A,B,q,r,b);
	return 0;	  

    }
}
