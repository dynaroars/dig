public class PLDI09_Fig4_5 {
    public static void vtrace0(int n, int m, int j, int i, int tCtr) {}
    public static void main(String[] args) {}
    
    public static int mainQ(int n, int m, int j) {
        assert (m > 0);
        assert (n > m);
        int i = m;
        int tCtr = 0;
        while (i > 0 && i < n) {
            vtrace0(n, m, j, i, tCtr);
            if (j > 0) {
                i++;
            } else {
                i--;
            }
            tCtr++;
        }
        return 0;
    }

}

