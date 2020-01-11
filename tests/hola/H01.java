public class H01 {
    public static void vtrace(int x, int y){}
    public static void main (String[] args){}

    public static void mainQ(int n){
	assert(n > 0);
	int x = 1;
	int y = 1;
	int j = 0;

	while (j < n) {
	    int t1 = x;
	    int t2 = y;
	    x = t1 + t2;
	    y = t1 + t2;
	    j = j + 1;
	}
	vtrace(x,y);

	//assert(y >= 1);
	  
    }


}

