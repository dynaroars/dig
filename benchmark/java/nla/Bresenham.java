public class Bresenham {
    public static void vtrace1(int X, int Y, int x, int y, int v){}
    public static void main (String[] args) {
    }
	
    public static int mainQ(int X, int Y){
        int v, x, y;
        v = 2 * Y - X;
        y = 0;
        x = 0;
        while (true) {
            //2*Y*x - 2*X*y - X + 2*Y - v == 0
            vtrace1(X,Y, x,y,v);
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


//Invariants: 

// 1. 2*Y*x - 2*X*y - X + 2*Y - v == 0
// 2. -y <= 0
// 3. -x + y <= 0
// 4. (y - 1) - max(Y, 0) <= 0
// 5. (x - 1) - max(X, 0) <= 0
