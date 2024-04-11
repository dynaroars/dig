public class Chanh1 {
    public static void vtrace1(int x, int n){}
    public static void vtrace2(int x, int n){}    
    public static void main (String[] args) {}
    public static int mainQ(int x, int n){
	assert (n>=0);
	//assert (x>0);
	
	while(true){
	    if(!(x != 0 && n>0)) break;
	    vtrace1(x,n);
	    x++;
	    n--;
	    
	}
	//vtrace2(x,n);
	//n = 0 & x >= 1
	return 0;
    }
}


/*

x > 0 <=> non-term

conj of oct 

x - y >= c0  

precond(inps) => nonterm
precond(ijnps) => term

*/
