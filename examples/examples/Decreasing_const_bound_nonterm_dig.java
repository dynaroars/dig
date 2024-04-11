public class Decreasing_const_bound_nonterm_dig {
    public static void vtrace1(int x) {
        // System.out.println("vtrace1: " + x);
    }
    public static void vtrace2(int x) {
        // System.out.println("vtrace2: " + x);
    }
    public static void vtrace3(int x) {
        // System.out.println("vtrace3: " + x);
    }
    public static void main (String[] args) {
        // int bnd = Integer.parseInt(args[0]);
        // int x = Nondet.getInt();
        // mainQ(bnd, x);
    }
    public static void mainQ(int x) {
        while (x >= 0) {
            x = x + 1;
        }
    }
}
