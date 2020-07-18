public class Ex5Test {
    public static void vtrace1_post(int M, int N, int P, int tCtr, int x, int y, int r, int t, int a, int b, int c, int d){}
    public static void main (String[] args) {}
    public static int mainQ(int M, int N, int P){
        assert (0 <= M);
        assert (0 <= N);
        assert (0 <= P);

        int tCtr = 0;
        int x = 2*M;
        int y = 2*N;
        int r = 2*P;
        int t = 2*tCtr;
        int a = M*M;
        int b = N*N;
        int c = P*P;
        int d = tCtr*tCtr;
        if (N == 0 || M == 0 || P == 0){
            tCtr = 0;
            t = 2*tCtr;
            d = tCtr*tCtr;
        }
        else if (N <= P && M > 0){
            tCtr = P + M + 1;
            t = 2*tCtr;
            d = tCtr*tCtr;
        }
        // else if (N > P || M == 0){
        //     tCtr = N - M*(P-N);
        // }
        vtrace1_post(M, N, P, tCtr, x, y, r, t, a, b, c, d);

        return 0;
    }
}
