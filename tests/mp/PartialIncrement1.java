public class PartialDecrement1 {
    public static void vtrace_loop(int i, int p, int q){}
    public static void vtrace_post(int i, int p, int q){}
    public static void main (String[] args) {}
     
    public static void mainQ(int p, int q) {
	int i = p;
	while(true){
	    vtrace_loop(i,p,q);
	    
	    if (!(i<q)){break;}
	    i = i + 1;
	}
  
	vtrace_post(i,p,q);
    }
}
