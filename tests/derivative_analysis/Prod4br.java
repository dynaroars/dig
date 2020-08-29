import java.util.LinkedList;
import java.util.Scanner;

public class Prod4br {
    public static void vtrace1(int x, int y, int a, int b, int p, int q){}
    public static void vtrace2(int x, int y, int a, int b, int p, int q){}
    public static void main (String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.println("x:");
        int x = sc.nextInt();
        System.out.println("y:");
        int y = sc.nextInt();
        mainQ(x,y);
    }
    public static int mainQ(int x, int y){
        assert(x>=1);
        assert(y>=1);

        int a,b,p,q;

        a = x;
        b = y;
        p = 1;
        q = 0;
        LinkedList<Integer> xlist = new LinkedList<>();
        LinkedList<Integer> ylist = new LinkedList<>();
        LinkedList<Integer> alist = new LinkedList<>();
        LinkedList<Integer> blist = new LinkedList<>();
        LinkedList<Integer> plist = new LinkedList<>();
        LinkedList<Integer> qlist = new LinkedList<>();
        LinkedList<Integer> counter = new LinkedList<>();
        int i =0;

        while(true) {
            //assert(q+a*b*p==x*y);
            vtrace1(x, y, a, b, p, q);

            xlist.add(x);
            ylist.add(y);
            alist.add(a);
            blist.add(b);
            plist.add(p);
            qlist.add(q);
            counter.add(i);
            i++;

            if(!(a!=0 && b!=0)) break;

            if (a % 2 ==0 && b % 2 ==0 ){
                a = a/2;
                b = b/2;
                p = 4*p;
            }
            else if (a % 2 ==1 && b % 2 ==0 ){
                a = a-1;
                q = q+b*p;
            }
            else if (a % 2 ==0 && b % 2 ==1 ){
                b = b-1;
                q = q+a*p;
            }
            else {
                a = a-1;
                b = b-1;
                q = q+(a+b+1)*p;
            }
        }

        System.out.println("['x', 'y', 'a', 'b', 'p', 'q', 'i'],"+xlist+","+ylist+","+alist+","+blist+","+plist+","+qlist+","+counter);

        //assert(q == x*y);
        //vtrace2(x, y, a, b, p, q);
        return q;
    }
}