public class MannaDiv {
    public static void vtrace1(int q, int t1, int t2, int x, int y){}
    public static void vtrace2(int q, int t1, int x, int y){}    
    public static void main (String[] args) {}

    public static int mainQ(int x, int y){
	assert (x >= 0);
	assert (y != 0);
     
	int q, t1, t2;
	q = 0;
	t1 = 0;
	t2 = x;

	while(true) {
	    //assert(q* y + t1 + t2 == x);
	    vtrace1(q, t1, t2, x, y);
	  
	    if(!(t2 != 0)) break;
	  
	    if (t1 + 1 == y) {
		q = q + 1;
		t1 = 0;
		t2 = t2 - 1;
	    }
	    else {
		t1 = t1 + 1;
		t2 = t2 - 1;
	    }
	}
	//assert y*q - x + t1 == 0
	//t2 guarantees to be 0
	vtrace2(q, t1, x, y); 
	//assert(q == x / y);
	return q;
    }
}
