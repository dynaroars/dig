public class H04 {
    public static void vtrace(int y){}
    public static void main (String[] args){}

    public static void mainQ(int y){
	int x = -50;

	while (x < 0) {
	    x = x + y;
	    y++;
	}

	vtrace(y);
	//assert(y > 0);
    }
}

