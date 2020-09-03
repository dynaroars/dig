public class H23 {

    public static void vtrace(int s){}
    public static void main (String[] args) {}

    public static void mainQ(int i, int n) {
	assert(n >= 0);
	int s = 0;
	for (i = 0; i < n; ++i) {
	    s = s + i;
	}
	vtrace(s);
	//assert(s >= 0);
    }
}
