public class Freire1 {
    public static void vtrace1(float a, float x, float r){}
    public static void vtrace2(float a, float x, float r){}
    
    public static void main (String[] args) {
    }

    public static void mainQ(float a) {
	float x = a/2.0f;
	float r = 0;

	while(true){
	    vtrace1(a,x,r);
	    //assert((float)a == 2*x + r*r - r); 
	    if (!(x>r)) break;
	    x = x - r;
	    r = r + 1;
	}

	vtrace2(a,x,r);
	//assert((float)a == 2*x + r*r - r); 
	//return r;	  
    }
}
