public class H02 {
    public static void vtrace(int x, int y){}
    public static void main (String[] args){}

    public static void mainQ(int n){
	assert(n > 0);
	int i = 1;
	int j = 0;
	int z = i - j;
	int x = 0;
	int y = 0;
	int w = 0;
	int u = 0;

	while (u < n) {
	    z += x + y + w;
	    y++;
	    if (z % 2 == 1) x++;
	    w += 2;
	    u = u + 1;
	}
	vtrace(x, y);
	//assert(x == y);	  
    }
}

