public class Freire1_Int {
    public static void vtrace1(int a, int x, int r){}
    public static void vtrace2(int a, int x, int r){}
    
    public static void main (String[] args) {
    }

    public static void mainQ(int x) {
	int a = x * 2;
	int r = 0;

	while(true){
	    vtrace1(a,x,r);
	    //assert((int)a == 2*x + r*r - r); 
	    if (!(x>r)) break;
	    x = x - r;
	    r = r + 1;
	}

	vtrace2(a,x,r);
	//assert((int)a == 2*x + r*r - r); 
	//return r;	  
    }
}
