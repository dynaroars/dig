public class PartialDecrement4 {
    public static void vtrace_loop1(int i, int p, int q,
				    int r, int s, int t){}
    public static void vtrace_loop2(int i, int p, int q,
				    int r, int s, int t){}
    public static void vtrace_loop3(int i, int p, int q,
				    int r, int s, int t){}    
    public static void vtrace_loop4(int i, int p, int q,
				    int r, int s, int t){}    
    public static void vtrace_post(int i, int p, int q,
				   int r, int s, int t){}
    public static void main (String[] args) {}
     
    public static void mainQ(int p, int q, int r, int s, int t) {
	int i = p;
	while(true){
	    // vtrace_loop1(i,p,q,r,s,t);
	    
	    if (!(i>q)){break;}
	    i = i - 1;
	}

	while(true){
	    // vtrace_loop2(i,p,q,r,s,t);
	    
	    if(!(i>r)){break;}
	    i = i - 1;
	}

	while(true){
	    // vtrace_loop3(i,p,q,r,s,t);
	    
	    if(!(i>s)){break;}
	    i = i - 1;
	}

	while(true){
	    // vtrace_loop4(i,p,q,r,s,t);
	    
	    if(!(i>t)){break;}
	    i = i - 1;
	}
	
	//assert(i==min(min(min(min(p,q),r),s),t));
	vtrace_post(i,p,q,r,s,t);
    }
}
