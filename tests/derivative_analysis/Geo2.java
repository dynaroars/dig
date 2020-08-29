import java.util.LinkedList;
import java.util.Scanner;

public class Geo2 {
    public static void vtrace1(int x, int y, int z, int k){}
    public static void vtrace2(int x, int y, int z, int k){}
    public static void main (String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.println("z:");
        int z = sc.nextInt();
        System.out.println("k:");
        int k = sc.nextInt();
        mainQ(z,k);
    }

    public static int mainQ(int z, int k){
        //if too large then might cause overflow
        assert(z>=0);
        assert(z<=10);
        assert(k>0);
        assert(k<=10);
        int x = 1; int y = 1; int c = 1;
        LinkedList<Integer> xlist = new LinkedList<>();
        LinkedList<Integer> ylist = new LinkedList<>();
        LinkedList<Integer> zlist = new LinkedList<>();
        LinkedList<Integer> klist = new LinkedList<>();
        LinkedList<Integer> counter = new LinkedList<>();
        int i = 0;

        while (true){
            //assert(1+x*z-x-z*y==0);
            vtrace1(x, y, z, k);
            xlist.add(x);
            ylist.add(y);
            zlist.add(z);
            klist.add(k);
            counter.add(i);
            i++;

            if(!(c < k)) break;
            c = c + 1;
            x = x*z + 1;
            y = y*z;
        }

        System.out.println("['x', 'y', 'z', 'k', 'i'],"+xlist+","+ylist+","+zlist+","+klist+","+counter);

        //assert(1+x*z-x-z*y==0);
        vtrace2(x,y,z,k);
        return x;
    }
}