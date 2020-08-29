import java.util.LinkedList;
import java.util.Scanner;

public class Dijkstra {
    public static void vtrace2(int r, int p, int n, int q, int h){}
    public static void vtrace3(int r, int p, int n, int h){}
    public static void main (String[] args) {
        Scanner scanner = new Scanner(System.in);
        System.out.println("n: ");
        int n = scanner.nextInt();
        mainQ(n);
    }

    public static int mainQ(int n){
        LinkedList<Integer> rList = new LinkedList<>();
        LinkedList<Integer> pList = new LinkedList<>();
        LinkedList<Integer> nList = new LinkedList<>();
        LinkedList<Integer> qList = new LinkedList<>();
        LinkedList<Integer> hList = new LinkedList<>();
        LinkedList<Integer> counter = new LinkedList<>();
        int p,q,r,h;
        p = 0;
        q = 1;
        r = n;
        h = 0;
        int i = 0;
        while (true){
            //vtrace1(r,p,n,q,h);
            if(!(q <= n)) break;
            q = 4 * q;
        }
        //q = 4^n

        while (true){
            //assert(r < 2*p + q);
            //assert(p*p + r*q == n*q);
            //assert((h*h*h) - 12*h*n*q + 16*n*p*q - h*(q*q) - 4*p*(q*q) + 12*h*q*r - 16*p*q*r == 0);
            //assert((h*h)*n - 4*h*n*p + 4*(n*n)*q - n*(q*q) - (h*h)*r + 4*h*p*r - 8*n*q*r + (q*q)*r + 4*q*(r*r) == 0);
            //assert((h*h)*p - 4*h*n*q + 4*n*p*q - p*(q*q) + 4*h*q*r - 4*p*q*r == 0 u, (p*p) - n*q + q*r == 0);
            vtrace2(r,p,n,q,h);
            rList.add(r);
            pList.add(p);
            nList.add(n);
            qList.add(q);
            hList.add(h);
            counter.add(i);
            i++;
            if(!(q!=1)) break;

            q = q / 4;
            h = p + q;
            p = p / 2;
            if (r >= h){
                p = p + q;
                r = r - h;
            }
        }
        System.out.println("['r', 'p', 'n', 'q', 'h', 'i'],"+rList+","+pList+","+nList+","+qList+","+hList+","+counter);
        //not tracking q, guaratted to be 1
        //assert(h*h*h - 12*h*n + 16*n*p + 12*h*r - 16*p*r - h - 4*p == 0);
        //assert(p*p - n + r == 0);
        //assert(h*h*p - 4*h*n + 4*n*p + 4*h*r - 4*p*r - p == 0);
        vtrace3(r,p,n,h);
        return p;
    }


}