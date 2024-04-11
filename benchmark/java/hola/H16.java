public class H16 {
    public static void vtrace(int i, int j, int y){}
    public static void main (String[] args) {}

    public static void mainQ(int i, int j) { 
	int x = i;
	int y = j;

	while (x != 0) {
	    x--;
	    y--;
	}
	if (i==j){
	vtrace(i, j, y);
	//%%%traces: int i, int j, int y
	//if (i == j) assert(y == 0);
	}
    }
}
