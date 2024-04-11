public class H25 {

    public static void vtrace(int i, int j){}
    
    public static void main (String[] args) {}

    public static void mainQ(int u1, int u2) {
	int x = 0;
	int y = 0;
	int i = 0;
	int j = 0;
	int i1 = 0;
	int i2 = 0;

	while (i1 < u1) {
	    i1++;
	    i2 = 0;
	    while (i2 < u2) {
		i2++;
		if (x == y)
		    i++;
		else
		    j++;
	    }

	    if (i >= j) {
		x++;
		y++;
	    } else
		y++;
	}
  
	vtrace(i, j);
	//assert(i >= j);
    }
}
