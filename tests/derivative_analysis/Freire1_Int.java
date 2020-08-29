import java.util.LinkedList;
import java.util.Scanner;

public class Freire1_Int {
    public static void vtrace1(int a, int x, int r){}
    public static void vtrace2(int a, int x, int r){}

    public static void main (String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.println("x:");
        int x = sc.nextInt();
        mainQ(x);
    }

    public static void mainQ(int x) {
        int a = x * 2;
        int r = 0;
        LinkedList<Integer> alist = new LinkedList<>();
        LinkedList<Integer> xlist = new LinkedList<>();
        LinkedList<Integer> rlist = new LinkedList<>();
        LinkedList<Integer> counter = new LinkedList<>();
        int i = 0;
        while(true){
            vtrace1(a,x,r);

            alist.add(a);
            xlist.add(x);
            rlist.add(r);
            counter.add(i);
            i++;
            //assert((int)a == 2*x + r*r - r);
            if (!(x>r)) break;
            x = x - r;
            r = r + 1;
        }
        System.out.println("['a', 'x', 'r', 'i'],"+alist+","+xlist+","+rlist+","+counter);

        vtrace2(a,x,r);
        //assert((int)a == 2*x + r*r - r);
        //return r;
    }
}