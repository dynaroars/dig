public class PartialIncrement3 {
    // public static void vtrace_loop1(int i, int p, int q, int r, int s){}
    // public static void vtrace_loop2(int i, int p, int q, int r, int s){}
    // public static void vtrace_loop3(int i, int p, int q, int r, int s){}    
    public static void vtrace_post(int i, int p, int q, int r, int s){}
    public static void main (String[] args) {}
     
    public static void mainQ(int p, int q, int r, int s) {
	int i = p;
	while(true){
	    // vtrace_loop1(i,p,q,r,s);
	    
	    if (!(i<q)){break;}
	    i = i + 1;
	}

	while(true){
	    // vtrace_loop2(i,p,q,r,s);
	    
	    if(!(i<r)){break;}
	    i = i + 1;
	}

	while(true){
	    // vtrace_loop3(i,p,q,r,s);
	    
	    if(!(i<s)){break;}
	    i = i + 1;
	}
	
	vtrace_post(i,p,q,r,s);
    }
}
