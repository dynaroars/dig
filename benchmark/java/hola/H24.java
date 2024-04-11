public class H24 {
    public static void vtrace(int k, int i){}
    public static void main (String[] args) {}

    public static void mainQ(int j, int k, int n) {
	int i = 0;

	for (i = 0; i < n; i++) {

	    for (j = i; j < n; j++) {

		for (k = j; k < n; k++) {
		    vtrace(k, i);
		    //assert(k >= i);
		}
	    }
	}
    }
}
