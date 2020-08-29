import java.util.LinkedList;
import java.util.Scanner;

public class Sqrt1 {
    public static void vtrace1(int a, int n, int t, int s){}
    public static void vtrace2(int a, int n, int t, int s){}
    public static void main (String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.println("n:");
        int n = sc.nextInt();
        mainQ(n);
    }

    public static int mainQ(int n){
        //for a to be sqrt of n,  needs to assume that n >= 0
        //assert(n >= 0);

        int a,s,t;
        a=0;
        s=1;
        t=1;

        int ctr = 0;

        LinkedList<Integer> alist = new LinkedList<>();
        LinkedList<Integer> nlist = new LinkedList<>();
        LinkedList<Integer> tlist = new LinkedList<>();
        LinkedList<Integer> slist = new LinkedList<>();
        LinkedList<Integer> counter = new LinkedList<>();
        int i = 0;

        while(true){
            //assert(t == 2*a + 1);
            //assert(s == (a + 1)*(a + 1));
            //assert(4s == t*t + 2*t + 1);
            vtrace1(a, n, t, s);
            alist.add(a);
            nlist.add(n);
            tlist.add(t);
            slist.add(s);
            counter.add(i);
            i++;
            if(!(s <= n)) break;
            a=a+1;
            t=t+2;
            s=s+t;
        }
        vtrace2(a, n, t, s);
	/*
	  2*a - t + 1 == 0
	  (t*t) - 4*s + 2*t + 1 == 0
	*/
        System.out.println("['a', 'n', 't', 's', 'i'],"+alist+","+nlist+","+tlist+","+slist+","+counter);

        return a;

    }

}