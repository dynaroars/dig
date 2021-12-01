public class Bresenham {
    public static void vtraces1(int X, int Y, int v, int x, int y) {
    }

    public static void main(String[] args) {
        mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
    }

    public static int mainQ(int X, int Y) {
        int v, x, y;
        v = 2 * Y - X;
        y = 0;
        x = 0;
        while (true) {
            //2*Y*x - 2*X*y - X + 2*Y - v == 0
            vtraces1(X,Y, x, y, v);
            System.out.printf("l0: X=%d, Y=%d, x=%d, y=%d, v=%d\n", X, Y, x, y, v);
            
            if (!(x <= X))
                break;
            //store results in out
            //out[x] = y	
            if (v < 0) {
                v = v + 2 * Y;
            } else {
                v = v + 2 * (Y - X);
                y++;
            }
            x++;
        }
        // 2*Y*x - 2*x*y + 2*Y - v - x + 2*y + 1 == 0
        return 0;
    }
}
