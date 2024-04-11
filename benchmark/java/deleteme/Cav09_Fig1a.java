public class Cav09_Fig1a {
	public static void vtrace_post(int m, int tCtr) {
	}

	public static void vtrace1(int x, int y, int m, int tCtr) {
	}

	public static void main(String[] args) {
	}

	public static int mainQ(int m) {
		int x = 0;
		int y = 0;
		int tCtr = 0;
		while (true) {
			if (!(x < 100))
				break;
			vtrace1(x, y, m, tCtr);
			//1. tCtr - x - y == 0
			//2. m*x*y - x*y^2 == 0
			if (y < m) {
				y++;
			} else {
				x++;
			}
			tCtr++;
		}
		//vtrace_post(m, tCtr);
		//%%%traces: int m, int t
		//dig2: m*t - (t*t) - 100*m + 200*t - 10000 == 0
		//solve for t: t == m + 100, t == 100
		return 0;
	}
}
