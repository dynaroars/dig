import java.util.LinkedList;
import java.util.Scanner;

public class Fermat1 {
    public static void vtraces1(int A, int R, int u, int v, int r){}
    public static void vtraces2(int A, int R, int u, int v, int r){}
    public static void vtraces3(int A, int R, int u, int v, int r){}
    public static void vtraces4(int A, int R, int u, int v){}
    public static void main (String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.println("A:");
        int A = sc.nextInt();
        System.out.println("R:");
        int R = sc.nextInt();
        mainQ(A,R);
    }

    public static int mainQ(int A, int R){
        assert((R - 1) * (R - 1) < A);
        //assert(A <= R*R);
        assert(A % 2 ==1);

        int u, v, r;
        u = 2*R + 1;
        v = 1;
        r = R*R - A;
        int i = 0;
        LinkedList<Integer> Alist = new LinkedList<>();
        LinkedList<Integer> Rlist = new LinkedList<>();
        LinkedList<Integer> ulist = new LinkedList<>();
        LinkedList<Integer> vlist = new LinkedList<>();
        LinkedList<Integer> rlist = new LinkedList<>();
        LinkedList<Integer> counter = new LinkedList<>();


        while (true){
            //assert(4*(A+r) == u*u-v*v-2*u+2*v);
            vtraces1(A, R, u, v, r);
            Alist.add(A);
            Rlist.add(R);
            ulist.add(u);
            vlist.add(v);
            rlist.add(r);
            counter.add(i);
            i++;
            if(!(r!=0)) break;

            while (true){
                //assert(4*(A+r) == u*u-v*v-2*u+2*v);
                vtraces2(A, R, u, v, r);
                if(!(r>0 )) break;
                r=r-v;
                v=v+2;
            }

            while (true){
                //assert(4*(A+r) == u*u-v*v-2*u+2*v);
                vtraces3(A, R, u, v, r);
                if(!(r<0 )) break;
                r=r+u;
                u=u+2;
            }

        }
        System.out.println("['A', 'R', 'u', 'v', 'r', 'i'],"+Alist+","+Rlist+","+ulist+","+vlist+","+rlist+","+counter);
        //assert(u!=v);

        //assert(4*A = u*u - v*v  - 2*u + 2*v);
        //do not consider r as it is guaranteed to be 0
        vtraces4(A, R, u, v);

        return (u-v)/2;
    }
}