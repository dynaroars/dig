public class PartialDecrement1 {
    public static void vtrace_loop(int i, int p, int q){}
    public static void vtrace_post(int i, int p, int q){}
    public static void main (String[] args) {}
     
    public static void mainQ(int p, int q) {
	int i = p;
	while(true){
	    /*
	    assert(i >= min(p,q));
	    assert(i <= max(p,q));
	    DIG:
	    p>=i
	    i >= min(p,q)
	    */
	    vtrace_loop(i,p,q);
	    
	    if (!(i>q)){break;}
	    i = i - 1;
	}
  
	/*
	  assert(i==min(p,q));
	  DIG
	  1: lambda i,p: p >= i
	  2: lambda i,q: q >= i
	  4: lambda i,p,q: i >= min(p,q) ***

	  sage: f1;f2; prove(f1 == f2)
	  If(p <= q, i == p, i == q)
	  And(If(p <= q, p <= i, q <= i), p >= i, q >= i)
	  proved
	*/

	vtrace_post(i,p,q);
    }
}
