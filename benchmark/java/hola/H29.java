public class H29 {
    public static void vtrace(int a, int b, int c, int d){}
    public static void main (String[] args) {}

    public static void mainQ(int u1, int u2) {
	assert(u1 > 0 && u2 > 0);
	
	int a = 1;
	int b = 1;
	int c = 2;
	int d = 2;
	int x = 3;
	int y = 3;
	int i1 = 0;
	int i2 = 0;

	while (i1 < u1) {
	    i1++;
	    x = a + c;
	    y = b + d;

	    if ((x + y) % 2 == 0) {
		a++;
		d++;
	    } else {
		a--;
	    }
    
	    i2 = 0;
	    while (i2 < u2 ) {
		i2++;
		c--;
		b--;
	    }
	}

	vtrace(a, b, c, d);
	//assert(a + c == b + d);
    }
}
