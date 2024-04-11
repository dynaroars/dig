public class H21 {
    public static void vtrace(int k, int n){}
    public static void main (String[] args) {}

    public static void mainQ(int n, int j, int v, int u4) {
	assert(n > 0);
	assert(n < 10);

	int c1 = 4000;
	int c2 = 2000;

	int k = 0;
	int i = 0;
	while (i < n) {
	    i++;
	    if (u4 !=0)
		v = 0;
	    else
		v = 1;

	    if (v == 0)
		k += c1;
	    else
		k += c2;
	}
  
	//%%%traces: int k, int n, int j, int v
	vtrace(k, n);
	//assert(k > n);
    }
}
