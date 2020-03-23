public class H10 {
    public static void vtrace(int x, int y){}
    public static void main (String[] args) {
	mainQ(Integer.parseInt(args[0]));
    }

    public static void mainQ(int u1){
	assert(u1 > 0);
	int i1 = 0;
	int w = 1;
	int z = 0;
	int x = 0;
	int y = 0;

	while (i1 < u1) {
	    i1++;
	    if (w == 1) {
		x++;
		w = 0;
	    };
	    if (z == 0) {
		y++;
		z = 1;
	    };
	}
	vtrace(x, y);
	//%%%traces: int x, int y, int u1
	//assert(x == y);	  
    }
}

