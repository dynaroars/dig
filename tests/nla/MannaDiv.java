public class MannaDiv {
    public static void vtrace1(int q, int a, int b, int x, int y){}
    public static void vtrace2(int q, int a, int x, int y){}    
    public static void main (String[] args) {}

    public static int mainQ(int x, int y){
	assert (x >= 0);
	assert (y != 0);
     
	int q, a, b;
	q = 0;
	a = 0;
	b = x;

	while(true) {
	    //assert(q* y + a + b == x);
	    vtrace1(q, a, b, x, y);
	  
	    if(!(b != 0)) break;
	  
	    if (a + 1 == y) {
		q = q + 1;
		a = 0;
		b = b - 1;
	    }
	    else {
		a = a + 1;
		b = b - 1;
	    }
	}
	//assert y*q - x + a == 0
	//b guarantees to be 0
	vtrace2(q, a, x, y); 
	//assert(q == x / y);
	return q;
    }
}
