public class H20 {

    public static void vtrace(int x, int y, int k, int n, int m){}
    public static void main (String[] args) {}

    public static void mainQ(int k, int x, int y, int i, int n, int u1) {
	assert((x + y) == k);

	int m = 0;
	int j = 0;
	while (j < n) {
	    if (j == i) {
		x++;
		y--;
	    } else {
		y++;
		x--;
	    }
	    if (u1 != 0) m = j;
	    j++;
	}
	vtrace(x, y, k, n, m);
	//assert((x + y) == k);
	//if (n > 0) {
	//  assert(0 <= m);
	//  assert(m < n);
	//}    
    }
}
