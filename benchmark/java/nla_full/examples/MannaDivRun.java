public class MannaDivRun {
    public static void vtrace1(int q, int a, int b, int x, int y){
	System.out.println("q " + q + " a " + a + " b " + b + " x " + x + " y " + y);
    }
    public static void vtrace2(int q, int a, int b, int x, int y){
	System.out.println("end: q " + q + " a " + a + " b " + b + " x " + x + " y " + y);
    }

    public static void main (String[] args) {
	int x = Integer.parseInt(args[0]);
	int y = Integer.parseInt(args[1]);
	
	assert (x >= 0);
	assert (y >= 1);
	
	//fake
	assert(x != 0);
	assert(y==1);
	
     
	int q, a, b;
	q = 0;
	a = 0;
	b = x;

	while(b != 0) {
	    //assert(q* y + a + b == x);
	    vtrace1(q, a, b, x, y);
	  
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
	vtrace2(q, a, b, x, y); 
	//assert(q == x / y);
    }
}
