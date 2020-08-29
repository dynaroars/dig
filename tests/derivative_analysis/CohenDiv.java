import java.util.LinkedList;
import java.util.Scanner;

public class CohenDiv {
    public static void vtrace1(int q, int r, int a, int b, int x, int y){}
    public static void vtrace2(int q, int r, int a, int b, int x, int y){}
    public static void vtrace3(int x, int y, int q, int r){}

    public static void main (String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.println("x:");
        int x = sc.nextInt();
        System.out.println("y:");
        int y = sc.nextInt();
        mainQ(x,y);
    }


    public static int mainQ(int x, int y) {
        //assert(y >= 1);
        assert(x >= 1);
        assert(y >= 1);

        int q=0;
        int r=x;
        int a=0;
        int b=0;
        int i = 0;

        LinkedList<Integer> qlist = new LinkedList<>();
        LinkedList<Integer> rlist = new LinkedList<>();
        LinkedList<Integer> alist = new LinkedList<>();
        LinkedList<Integer> blist = new LinkedList<>();
        LinkedList<Integer> xlist = new LinkedList<>();
        LinkedList<Integer> ylist = new LinkedList<>();
        LinkedList<Integer> counter = new LinkedList<>();


        while(true) {
            //assert(q*y + r == x);
            //assert(a*y == b);
            vtrace1(q,r,a,b,x,y);

            if(!(r>=y)) break;
            a=1;
            b=y;

            while (true) {
                //assert(q*y + r == x);
                //assert(a*y == b);
                qlist.add(q);
                rlist.add(r);
                alist.add(a);
                blist.add(b);
                xlist.add(x);
                ylist.add(y);
                counter.add(i);
                i++;

                vtrace2(q,r,a,b,x,y);
                if(!(r >= 2*b)) break;

                a = 2*a;
                b = 2*b;
            }
            r=r-b;
            q=q+a;
        }
        System.out.println("['q', 'r', 'a', 'b', 'x', 'y', 'i'],"+qlist+","+rlist+","+alist+","+blist+","+xlist+","+ylist+","+counter);
        //assert(q*y + r == x);
        vtrace3(x,y,q,r);
        return q;
    }
}