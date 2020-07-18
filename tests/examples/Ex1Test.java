public class Ex1Test {
    public static void vtrace1_post(int m, int tCtr, int x, int y, int a, int b, int c){}
    public static void vtrace0(int m, int n){}
    public static void main (String[] args) {}
    public static int mainQ(int m, int n){
        // if (m > 1 && n <= 20 && 2*n*n + 3*m == 62){
        //     vtrace0(m,n);
        // }

        int tCtr = 0;
        int x = m*2;
        int y = tCtr*2;
        int a = m*m;
        int b = tCtr*tCtr;
        int c = m*tCtr;
        if (m < 0){
            tCtr = -10;
            y = tCtr*2;
            b = tCtr*tCtr;
            c = m*tCtr;
        }
        else if (m == 0){
            tCtr = 5;
            y = tCtr*2;
            b = tCtr*tCtr;
            c = m*tCtr;
        }
        else{ // m > 0
            tCtr = m  + 7;
            y = tCtr*2;
            b = tCtr*tCtr;
            c = m*tCtr;
        }
        vtrace1_post(m, tCtr, x,y,a,b,c);

        return 0;
    }
}


