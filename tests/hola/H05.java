public class H05 {
    public static void vtrace(int i, int j){}
    public static void main (String[] args) {}

    public static void mainQ(int flag, int n){
	assert(n > 0);
	int j = 0;
	int i = 0;
	int x = 0;
	int y = 0;
	int u = 0;

	while (u < n) {
	    u++;
	    x++;
	    y++;
	    i += x;
	    j += y;
	    if (flag != 0) j += 1;
	}
	vtrace(i,j);
	//assert(j >= i);
    }
}
