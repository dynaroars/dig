import java.util.LinkedList;
import java.util.Scanner;

public class Bresenham {
    public static void vtrace1(int X, int Y, int x, int y, int v){}
    public static void vtrace2(int X, int Y, int x, int y, int v){}

    public static void main (String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.println("X:");
        int X = sc.nextInt();
        System.out.println("Y:");
        int Y = sc.nextInt();
        mainQ(X,Y);
    }

    public static int mainQ(int X, int Y){

        int v, x, y;
        v = 2 * Y - X;
        y = 0;
        x = 0;
        int i = 0;
        LinkedList<Integer> Xlist = new LinkedList<>();
        LinkedList<Integer> Ylist = new LinkedList<>();
        LinkedList<Integer> xlist = new LinkedList<>();
        LinkedList<Integer> ylist = new LinkedList<>();
        LinkedList<Integer> vlist = new LinkedList<>();
        LinkedList<Integer> counter = new LinkedList<>();
        while (true) {
            //2*Y*x - 2*X*y - X + 2*Y - v == 0
            Xlist.add(X);
            Ylist.add(Y);
            xlist.add(x);
            ylist.add(y);
            vlist.add(v);
            counter.add(i);
            vtrace1(X,Y, x,y,v);
            if (!(x <= X))
                break;

            if (v < 0) {
                v = v + 2 * Y;
            } else {
                v = v + 2 * (Y - X);
                y++;
            }
            x++;
            i++;
        }
        System.out.println("['X', 'Y', 'x', 'y', 'v', 'i'],"+Xlist+","+Ylist+","+xlist+","+ylist+","+vlist+","+counter);
        // 2*Y*x - 2*x*y + 2*Y - v - x + 2*y + 1 == 0
        vtrace2(X,Y, x,y,v);
        return 0;
    }
}