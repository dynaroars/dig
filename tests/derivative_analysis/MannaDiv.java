import java.util.LinkedList;
import java.util.Scanner;

public class MannaDiv {
    public static void vtrace1(int q, int a, int b, int x, int y){}
    public static void vtrace2(int q, int a, int x, int y){}
    public static void main (String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.println("x:");
        int x = sc.nextInt();
        System.out.println("y:");
        int y = sc.nextInt();
        mainQ(x,y);
    }

    public static int mainQ(int x, int y){
        assert(x >= 0);
        assert(y != 0);

        int q, a, b;
        q = 0;
        a = 0;
        b = x;

        LinkedList<Integer> qlist = new LinkedList<>();
        LinkedList<Integer> alist = new LinkedList<>();
        LinkedList<Integer> blist = new LinkedList<>();
        LinkedList<Integer> xlist = new LinkedList<>();
        LinkedList<Integer> ylist = new LinkedList<>();
        LinkedList<Integer> counter = new LinkedList<>();
        int i = 0;

        while(true) {
            //assert(q* y + a + b == x);
            vtrace1(q, a, b, x, y);

            qlist.add(q);
            alist.add(a);
            blist.add(b);
            xlist.add(x);
            ylist.add(y);
            counter.add(i);
            i++;


            if(!(b != 0)) break;

            if (a + 1 == y) {
                q = q + 1;
                a = 0;
                b = b - 1;
            }
            else {
                a = a + 1;
                b = b - 1;
            }
        }

        System.out.println("['q', 'a', 'b', 'x', 'y', 'i'],"+qlist+","+alist+","+blist+","+xlist+","+ylist+","+counter);


        //assert y*q - x + a == 0
        //b guarantees to be 0
        vtrace2(q, a, x, y);
        //assert(q == x / y);
        return q;
    }
}