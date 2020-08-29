import java.util.LinkedList;
import java.util.Scanner;

public class DivBin {
    public static void vtrace1(int A, int B, int q, int r, int b){}
    public static void vtrace2(int A, int B, int q, int r, int b){}
    public static void vtrace3(int A, int B, int q, int r, int b){}

    public static void main (String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.println("A:");
        int A = sc.nextInt();
        System.out.println("B:");
        int B = sc.nextInt();
        mainQ(A,B);
    }

    public static int mainQ(int A, int B) {
        assert(B >= 1);

        int q = 0;
        int r = A;
        int b = B;
        int i = 0;
        LinkedList<Integer> Alist = new LinkedList<>();
        LinkedList<Integer> Blist = new LinkedList<>();
        LinkedList<Integer> qlist = new LinkedList<>();
        LinkedList<Integer> rlist = new LinkedList<>();
        LinkedList<Integer> blist = new LinkedList<>();
        LinkedList<Integer> counter = new LinkedList<>();
        while(true){
            vtrace1(A,B,q,r,b);
            if (!(r >= b)) break;
            b=2*b;
        }

        while(true){
            //assert(A == q*b + r);
            vtrace2(A,B,q,r,b);
            Alist.add(A);
            Blist.add(B);
            qlist.add(q);
            rlist.add(r);
            blist.add(b);
            counter.add(i);
            i++;
            if (!(b!=B)) break;

            q = 2*q;
            b = b/2;
            if (r >= b) {
                q = q + 1;
                r = r - b;
            }
        }
        //_assert(A == q * b + r)
        vtrace3(A,B,q,r,b);
        System.out.println("['A', 'B', 'q', 'r', 'b', 'i'],"+Alist+","+Blist+","+qlist+","+rlist+","+blist+","+counter);
        return 0;

    }
}