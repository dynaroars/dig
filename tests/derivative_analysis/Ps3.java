import java.util.LinkedList;
import java.util.Scanner;

public class Ps3 {
    public static void vtrace1(int x, int y, int k){}
    public static void vtrace2(int x, int y, int k){}
    public static void main (String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.println("k:");
        int k = sc.nextInt();
        mainQ(k);
    }
    public static int mainQ(int k){
        assert (k>=0);
        assert (k<=30);

        int y = 0;
        int x = 0;
        int c = 0;

        LinkedList<Integer> xlist = new LinkedList<>();
        LinkedList<Integer> ylist = new LinkedList<>();
        LinkedList<Integer> klist = new LinkedList<>();
        LinkedList<Integer> counter = new LinkedList<>();
        int i = 0;

        while(true){
            //assert(6*x-2*y*y*y-3*y*y-y == 0);
            vtrace1(x, y, k);
            xlist.add(x);
            ylist.add(y);
            klist.add(k);
            counter.add(i);
            i++;
            if (!(c < k)) break;
            c = c +1 ;
            y=y +1;
            x=y*y+x;
        }

        System.out.println("['x', 'y', 'k', 'i'],"+xlist+","+ylist+","+klist+","+counter);

        //assert(6*x-2*y*y*y-3*y*y-y == 0);
        vtrace2(x,y,k);
        return x;
    }
}