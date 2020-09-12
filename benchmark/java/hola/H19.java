public class H19 {

    public static void vtrace(int y, int n){}
    public static void main (String[] args) {}

    public static void mainQ(int m, int n) {
	assert(n >= 0);
	assert(m >= 0);
	assert(m < n);

	int x = 0;
	int y = m;

	while (x < n) {
	    x++;
	    if (x > m) y++;
	}

	vtrace(y, n);
	//assert(y == n);
    }
}
