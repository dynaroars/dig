public class PartialIncrement2 {
    public static void vtrace_loop1(int i, int p, int q, int r){}
    public static void vtrace_loop2(int i, int p, int q, int r){}    
    public static void vtrace_post(int i, int p, int q, int r){}
    public static void main (String[] args) {}
     
    public static void mainQ(int p, int q, int r) {
	int i = p;
	while(true){
	    // assert(i >= min(p,q));
	    // assert(i <= max(p,q));

	    vtrace_loop1(i,p,q,r);
	    
	    if (!(i<q)){break;}
	    i = i + 1;
	}

	while(true){
	    vtrace_loop2(i,p,q,r);
	    
	    if(!(i<r)){break;}
	    i = i + 1;
	}

	vtrace_post(i,p,q,r);
    }
}
