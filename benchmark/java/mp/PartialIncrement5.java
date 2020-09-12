public class PartialIncrement5 {
    public static void vtrace_loop1(int i, int p, int q,
				    int r, int s, int t, int u){}
    public static void vtrace_loop2(int i, int p, int q,
				    int r, int s, int t, int u){}
    public static void vtrace_loop3(int i, int p, int q,
				    int r, int s, int t, int u){}    
    public static void vtrace_loop4(int i, int p, int q,
				    int r, int s, int t, int u){}    
    public static void vtrace_loop5(int i, int p, int q,
				    int r, int s, int t, int u){}    

    public static void vtrace_post(int i, int p, int q,
				   int r, int s, int t, int u){}
    public static void main (String[] args) {}
     
    public static void mainQ(int p, int q, int r, int s, int t, int u) {
		int i = p;
		while(true){
			vtrace_loop1(i,p,q,r,s,t,u);
			
			if (!(i<q)){break;}
			i = i + 1;
		}

		while(true){
			vtrace_loop2(i,p,q,r,s,t,u);
			
			if(!(i<r)){break;}
			i = i + 1;
		}

		while(true){
			vtrace_loop3(i,p,q,r,s,t,u);
			
			if(!(i<s)){break;}
			i = i + 1;
		}

		while(true){
			vtrace_loop4(i,p,q,r,s,t,u);
			
			if(!(i<t)){break;}
			i = i + 1;
		}

		while(true){
			vtrace_loop5(i,p,q,r,s,t,u);
			
			if(!(i<u)){break;}
			i = i + 1;
		}
		
		vtrace_post(i,p,q,r,s,t,u);
		}
}
