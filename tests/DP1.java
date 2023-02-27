public class DP1 {
    public static void vtrace0(int x, int y, int A, int B){}
    public static void vtrace(int x, int y, int A, int B){}
    public static void main (String[] args){}
    
    public static void mainQ(int A, int B){
        int x = A;
        int y = B;
        
        while (x < 100) {
            vtrace0(x,y,A,B);
            x = x + 1;
            y = y - 1;
        }
        vtrace(x,y,A,B);
    }
    
    
}
