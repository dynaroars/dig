public class Ex2Test {
    public static void vtrace1_post(int m, int tCtr, int x, int y/*, int a, int b, int c*/){}
    public static void main (String[] args) {}
    public static int mainQ(int m){
        int tCtr = 0;
        int x = 2*m;
        int y = 2*tCtr;/*
        int a = m*m;
        int b = tCtr*tCtr;
        int c = m*tCtr;*/
        if (m < 0){
            tCtr = -5;
            y = 2*tCtr;/*
            b = tCtr*tCtr;
            c = m*tCtr;*/
        }
        else if (m == 0){
            tCtr = 2;
            y = 2*tCtr;/*
            b = tCtr*tCtr;
            c = m*tCtr;*/
        }
        else{
            tCtr = m  + 5;
            y = 2*tCtr;/*
            b = tCtr*tCtr;
            c = m*tCtr;*/
        }
        vtrace1_post(m, tCtr, x,y/*, a, b, c*/);

        return 0;
    }
}
