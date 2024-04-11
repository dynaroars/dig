public class H17 {
    public static void vtrace(int k, int n){}
    public static void main (String[] args) {}

    public static void mainQ(int n){
	assert(n > 0);
	int k = 1;
	int i = 1;
	int j = 0;

	while (i < n) {
	    j = 0;
	    while (j < i) {
		k += (i - j);
		j++;
	    }
	    i++;
	}

	vtrace(k, n);
	//assert(k >= n);	  

    }
}

