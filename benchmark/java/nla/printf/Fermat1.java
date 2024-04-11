public class Fermat1 {
    public static void vtraces1(int A, int R, int u, int v, int r) {
    }

    public static void vtraces2(int A, int R, int u, int v, int r) {
    }

    public static void vtraces3(int A, int R, int u, int v, int r) {
    }

    public static void main(String[] args) {
        mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
    }

    public static int mainQ(int A, int R) {
        assert ((R - 1) * (R - 1) < A);
        // assert(A <= R*R);
        assert (A % 2 == 1);

        int u, v, r;
        u = 2 * R + 1;
        v = 1;
        r = R * R - A;

        int i = 0, j = 0, k = 0;
        while (true) {
            // if (u != v+ 2*R + 2*k - 2*j){
            // System.out.printf("l0 violation0: A=%d, R=%d, u=%d, v=%d, r=%d, i=%d, j=%d,
            // k=%d\n", A, R, u, v, r, i, j, k);
            // }
            // if (v != 1+2*j){
            // System.out.printf("l0 violation1: A=%d, R=%d, u=%d, v=%d, r=%d, i=%d, j=%d,
            // k=%d\n", A, R, u, v, r, i, j, k);
            // }
            // if(u != 2*R + 1 + 2*k){
            // System.out.printf("l0 violation2: A=%d, R=%d, u=%d, v=%d, r=%d, i=%d, j=%d,
            // k=%d\n", A, R, u, v, r, i, j, k);
            // }
            assert (4 * (A + r) == u * u - v * v - 2 * u + 2 * v);
            System.out.printf("l0: A=%d, R=%d, u=%d, v=%d, r=%d, i=%d, j=%d, k=%d\n", A, R, u, v, r, i, j, k);
            // vtraces1(A, R, u, v, r);
            if (!(r != 0))
                break;
            i++;

            while (true) {
                assert (4 * (A + r) == u * u - v * v - 2 * u + 2 * v);
                // System.out.printf("l1: A=%d, R=%d, u=%d, v=%d, r=%d, i=%d, j=%d, k=%d\n", A,
                // R, u, v, r, i, j, k);
                // vtraces2(A, R, u, v, r);
                if (!(r > 0))
                    break;
                j++;

                r = r - v;
                v = v + 2;
            }

            while (true) {
                assert (4 * (A + r) == u * u - v * v - 2 * u + 2 * v);
                // System.out.printf("l2: A=%d, R=%d, u=%d, v=%d, r=%d, i=%d, j=%d, k=%d\n", A,
                // R, u, v, r, i, j, k);
                // vtraces3(A, R, u, v, r);
                if (!(r < 0))
                    break;
                k++;

                r = r + u;
                u = u + 2;
            }

        }
        return (u - v) / 2;
    }
}
