public class H18 {
    public static void vtrace(int flag, int j){}
    public static void main (String[] args) {}

    public static void mainQ(int flag, int a) {
	int b = 0;
	int j = 0;	
	for (b = 0; b < 100; ++b) {
	    if (flag != 0) j = j + 1;
	}
	
	vtrace(flag, j);
	//if (flag != 0) assert(j == 100);

    }
}
