import java.util.LinkedList;
import java.util.Scanner;

public class Lcm1 {
    public static void vtrace1(int a, int b, int x, int y, int u, int v){}
    public static void vtrace2(int a, int b, int x, int y, int u, int v){}
    public static void vtrace3(int a, int b, int x, int y, int u, int v){}
    public static void vtrace4(int a, int b, int x, int y, int u, int v){}

    public static void main (String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.println("a:");
        int a = sc.nextInt();
        System.out.println("b:");
        int b = sc.nextInt();
        mainQ(a,b);
    }
    public static int mainQ(int a, int b){
        assert(a >= 1);
        assert(b >= 1);
        int x,y,u,v;
        x=a;
        y=b;
        u=b;
        v=0;

        LinkedList<Integer> alist = new LinkedList<>();
        LinkedList<Integer> blist = new LinkedList<>();
        LinkedList<Integer> xlist = new LinkedList<>();
        LinkedList<Integer> ylist = new LinkedList<>();
        LinkedList<Integer> ulist = new LinkedList<>();
        LinkedList<Integer> vlist = new LinkedList<>();
        LinkedList<Integer> counter = new LinkedList<>();
        int i = 0;
        while(true) {
            //assert(x*u + y*v == a*b);
            alist.add(a);
            blist.add(b);
            xlist.add(x);
            ylist.add(y);
            ulist.add(u);
            vlist.add(v);
            counter.add(i);
            i++;
            vtrace1(a, b, x, y, u, v);
            if (!(x != y)) break;

            while (true){
                //assert(x*u + y*v == a*b);
                vtrace2(a, b, x, y, u, v);
                if(!(x > y)) break;
                x = x - y;
                v = v + u;
            }

            while (true){
                //assert(x*u + y*v == a*b);
                vtrace3(a, b, x, y, u, v);
                if(!(x < y)) break;
                y = y - x;
                u = u + v;
            }
        }
        System.out.println("['a', 'b', 'x', 'y', 'u', 'v', 'i'],"+alist+","+blist+","+xlist+","+ylist+","+ulist+","+vlist+","+counter);

        //x==gcd(a,b)
        //a*b == u*y + v*y
        vtrace4(a,b,x,y,u,v);

        return u+v; //lcm
    }
}
