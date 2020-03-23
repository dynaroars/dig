public class H34 {

    public static void vtrace(int x, int y, int n, int i, int m) {}
    public static void main (String[] args) {
	mainQ(Integer.parseInt(args[0]));
    }

    public static void mainQ(int n){
	int x = 0;
	int y = 0;
	int i = 0;
	int m = 10;

	while (i < n) {
	    i++;
	    x++;
	    if (i % 2 == 0) y++;
	}
	//manual
  // if (i == m) {
	vtrace(x, y, n, i, m);
	//     // assert(x == 2 * y);
	// }

    }
}
