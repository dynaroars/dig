public class CohenDivFake {
    public static void vtrace0(int q, int r, int a, int b, int x, int y){}
    public static void main (String[] args) {}
    public static int mainQ(int q, int r, int a, int b, int x, int y){

        if(a*y - b == 0 && q*y + r - x == 0 &&
            -r <= 0 && -a <= 0 && -x <= -1 && 
            r - x <= 0 && a - q <= 0 && q - x <= 0 &&
            a - b <= 0 && b - x <= 0 && -a - y <= -1){
            vtrace0(q, r, a, b, x, y);
        }
        return 0;
    }
}

