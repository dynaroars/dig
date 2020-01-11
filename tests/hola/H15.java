public class H15 {

    public static void vtrace(int k){}
    public static void main (String[] args) {}

    public static void mainQ(int n, int k) {
	assert(n > 0);
	assert(k > n);

	int j = 0;
	while (j < n) {
	    j++;
	    k--;
	}

	vtrace(k);
	//assert(k >= 0);
    }
}
