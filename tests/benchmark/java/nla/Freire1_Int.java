public class Freire1_Int {
    public static void vtrace1(float a, float x, float r){}
    
    public static void main (String[] args) {
    }

    public static int mainQ(int x) {
	int a = x * 2;
	int r = 0;

	while(true){
	    vtrace1(a,x,r);
	    //assert((float)a == 2*x + r*r - r); 
	    if (!(x>r)) break;
	    x = x - r;
	    r = r + 1;
	}


	return r;	  
    }
}
