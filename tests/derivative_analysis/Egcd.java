import java.util.LinkedList;
import java.util.Scanner;

public class Egcd {
    public static void vtrace1(int x, int y, int a, int b, int p, int q, int r, int s){}
    public static void vtrace2(int x, int y, int a, int b, int p, int q, int r, int s){}
    public static void main (String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.println("x:");
        int x = sc.nextInt();
        System.out.println("y:");
        int y = sc.nextInt();
        mainQ(x,y);
    }

    public static int mainQ(int x, int y){
        /* extended Euclid's algorithm */
        assert(x >= 1);  //inf loop if remove
        assert(y >= 1);
        int a,b,p,q,r,s;

        a=x;
        b=y;
        p=1;
        q=0;
        r=0;
        s=1;
        int i = 0;

        LinkedList<Integer> xlist = new LinkedList<>();
        LinkedList<Integer> ylist = new LinkedList<>();
        LinkedList<Integer> alist = new LinkedList<>();
        LinkedList<Integer> blist = new LinkedList<>();
        LinkedList<Integer> plist = new LinkedList<>();
        LinkedList<Integer> qlist = new LinkedList<>();
        LinkedList<Integer> rlist = new LinkedList<>();
        LinkedList<Integer> slist = new LinkedList<>();
        LinkedList<Integer> counter = new LinkedList<>();

        while(true){
            //assert(1 == p*s - r*q);
            //assert(a == y*r + x*p);
            //assert(b == x*q + y*s);

            vtrace1(x,y,a,b,p,q,r,s);

            if(!(a!=b)) break;

            xlist.add(x);
            ylist.add(y);
            alist.add(a);
            blist.add(b);
            plist.add(p);
            qlist.add(q);
            rlist.add(r);
            slist.add(s);
            counter.add(i);
            i++;

            if (a>b) {
                a = a-b;
                p = p-q;
                r = r-s;
            }
            else {
                b = b-a;
                q = q-p;
                s = s-r;}
        }
        //assert(a - b == 0);
        //assert(p*x + r*y - b == 0);
        //assert(q*r - p*s + 1 == 0);
        //assert(q*x + s*y - b == 0);
        System.out.println("['x', 'y', 'a', 'b', 'p', 'q', 'r', 's', 'i'],"+xlist+","+ylist+","+alist+","+blist+","+plist+","+qlist+","+rlist+","+slist+","+counter);

        vtrace2(x,y,a,b,p,q,r,s);
        return a;
    }


}