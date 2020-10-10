public class H31 {
	
	public static void vtrace1(int j, int n, int i){}
	public static void vtrace2(int j, int n, int i){}
	public static void main (String[] args) {
		mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]));
	}
	
	public static void mainQ(int m, int n, int u1) {
		assert(m + 1 < n);
		int i = 0;
		int j = 0;
		int k = 0;
		for (i = 0; i < n; i += 4) {
			
			for (j = i; j < m;) {
				
				if (u1!=0) {
					//%%%traces: int m, int n, int u1, int i, int j
					vtrace1(j, n, i);
					//assert(j >= 0);
					j++;
					k = 0;
					while (k < j) {
						k++;
					}
				} else {
					//%%%traces: int m, int n, int u1, int i, int j
					vtrace2(j, n, i);
					//assert(n + j + 5 > i);
					j += 2;
				}
			}
		}
		////%%%traces: int n, int j, int i
		//vtrace(j, i, n);
	}
}
