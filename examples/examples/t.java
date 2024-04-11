public class Decreasing_const_bound_nonterm_dig {
    public static void vtrace1(int x) {
        // System.out.println("vtrace1: " + x);
    }
​
    public static void vtrace2(int x) {
        // System.out.println("vtrace2: " + x);
    }
​
    public static void vtrace3(int x) {
        // System.out.println("vtrace3: " + x);
    }
​
    public static void main (String[] args) {
        // int bnd = Integer.parseInt(args[0]);
        // int x = Nondet.getInt();
        // mainQ(bnd, x);
    }
​
    public static void mainQ(int bnd, int x) {
        vtrace1(x);
        // int counter = 0;
        while (x >= 0) {
            // if (counter > bnd) break;
            // else
            //     counter++;
            vtrace2(x);
            x = x + 1;
        }
        // if (counter <= bnd)
            vtrace3(x);
    }
}
