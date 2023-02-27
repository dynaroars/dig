public class H01 {
	public static void vtrace(int x, int y) {
	}

	public static void vtrace1(int y) {
	}

	public static void main(String[] args) {
	}

	public static void mainQ(int n) {
		assert (n > 0);
		assert (n <= 30); // will overflow (2^n) without this bound

		int x = 1;
		int y = 1;
		int j = 0;
		int t1 = 0;
		int t2 = 0;
		while (j < n) {
			t1 = x;
			t2 = y;
			x = t1 + t2;
			y = t1 + t2;
			j = j + 1;
		}
		vtrace(x, y);
		// vtrace1(y);
		// assert(y >= 1);

	}

}
