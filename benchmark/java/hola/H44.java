public class H44 {

    public static void vtrace(int j, int i, int flag){}
    public static void main (String[] args) {
	mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
    }

    public static void mainQ(int k, int flag) {
	int j = 0;
	int n = 0;

	if (flag == 1) {
	    n = 1;
	} else {
	    n = 2;
	}

	int i = 0;

	while (i <= k) {
	    i++;
	    j = j + n;
	}

	//%%%traces: int j, int i, int k, int flag

	if (flag == 1) {
	    vtrace(j, i, flag);
	    //assert(j==i)
	}
    }
}
