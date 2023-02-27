public class MP1 {
    public static void vtrace1(int x, int y) {
    }

    public static void vtrace2(int x, int y) {
    }

    public static void vtrace3(int x, int y, int z) {
    }

    public static void main(String[] args) {
    }

    public static int mainQ(int x, int y) {
	int z = 5;
	if (3 <= x && x <= 9) {
	    vtrace1(x, y);
	}
	if (x<=y){
	    vtrace2(x,y);
	}
	if (y<=x){
	    vtrace3(x,y,z);
	}

	return 0;
    }
}
