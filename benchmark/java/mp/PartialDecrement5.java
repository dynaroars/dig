public class PartialDecrement5 {
    public static void vtrace_post(int i, int p, int q,
				   int r, int s, int t, int u){}
    public static void main (String[] args) {}
     
    public static void mainQ(int p, int q, int r, int s, int t, int u) {
	int i = p;
	while(true){
	    if (!(i>q)){break;}
	    i = i - 1;
	}

	while(true){
	    if(!(i>r)){break;}
	    i = i - 1;
	}

	while(true){
	    if(!(i>s)){break;}
	    i = i - 1;
	}

	while(true){
	    if(!(i>t)){break;}
	    i = i - 1;
	}

	while(true){
	    if(!(i>u)){break;}
	    i = i - 1;
	}
	
	//assert(i==min(min(min(min(min(p,q),r),s),t),u));
	vtrace_post(i,p,q,r,s,t,u);
    }
}
