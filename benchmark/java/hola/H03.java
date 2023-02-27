public class H03 {

    public static void vtrace(int i){}
    public static void main (String[] args) {}
    
    public static void mainQ(int i, int n, int l) {
	assert(l > 0);
	int t = 0;
	int k = 0;

	for (k = 1; k < n; k++) {

	    for (i = l; i < n; i++) {
		t = t + 1;
	    }

	    for (i = l; i < n; i++) {
		
		vtrace(i);
		// assert(1 <= i)
		t = t + 1;
	    }
	}
	//%%%traces: int i, int k, int n, int l, int t
    }
}
