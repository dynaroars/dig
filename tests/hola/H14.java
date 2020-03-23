public class H14 {

    public static void vtrace(int a, int m){}
    public static void main (String[] args) {}

    public static void mainQ(int m, int u4) {
	assert(m > 0);

	int a = 0;
	int j = 0;
	for (j = 1; j <= m; j++) {
	    if (u4!=0)
		a++;
	    else
		a--;
	}

	vtrace(a, m);
	//assert(a >= 0 - m);
	//assert(a <= m);
    }
}
