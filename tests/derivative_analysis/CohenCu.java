import java.util.LinkedList;
import java.util.Scanner;

public class CohenCu {
    public static void vtrace1(int a, int n, int x, int y, int z){}
    public static void vtrace2(int a, int n, int x, int y, int z){}
    public static void main (String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.println("a:");
        int a  = sc.nextInt();
        mainQ(a);
    }

    public static int mainQ(int a) {
        int n,x,y,z;
        n=0; x=0; y=1; z=6;
        int i = 0;
        LinkedList<Integer> alist = new LinkedList<>();
        LinkedList<Integer> nlist = new LinkedList<>();
        LinkedList<Integer> xlist = new LinkedList<>();
        LinkedList<Integer> ylist = new LinkedList<>();
        LinkedList<Integer> zlist = new LinkedList<>();
        LinkedList<Integer> counter = new LinkedList<>();

        while(true){
            //assert(z == 6*n + 6);
            //assert(y == 3*n*n + 3*n + 1);
            //assert(x == n*n*n);
            //assert((z*z) - 12*y - 6*z + 12 == 0);
            //assert(y*z - 18*x - 12*y + 2*z - 6 == 0);
            alist.add(a);
            nlist.add(n);
            xlist.add(x);
            ylist.add(y);
            zlist.add(z);
            counter.add(i);

            vtrace1(a,n,x,y,z);
            if(!(n<=a)) break;

            n = n+1;
            x = x+y;
            y = y+z;
            z = z+6;
            i++;
        }
        System.out.println("['a', 'n', 'x', 'y', 'z', 'i'],"+alist+","+nlist+","+xlist+","+ylist+","+zlist+","+counter);

	/*
	  1. a*z - 6*a - 2*y + 2*z - 10 == 0 p
	  2. (z*z) - 12*y - 6*z + 12 == 0 p
	  3. 6*n - z + 6 == 0 p
	  4. y*z - 18*x - 12*y + 2*z - 6 == 0 p
	 */
        vtrace2(a,n,x,y,z);
        return x;
    }
}