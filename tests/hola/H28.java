public class H28 {
    public static void vtrace(int y, int n){}
    public static void main (String[] args) {}
    
    public static void mainQ(int u){
	assert(u > 0);
	int x = 0;
	int y = 0;
	int n = 0;
	int i0 = 0;

	while (i0 < u) {
	    x++;
	    y++;
	    i0++;
	}

	while (x != n) {
	    x--;
	    y--;
	}
	//%%%traces: int y, int n, int x, int u, int i0
	vtrace(y, n);
	//assert(y == n);
    }
}

