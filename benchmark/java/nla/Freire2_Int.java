public class Freire2_Int {
  public static void vtrace1(float a, float x, int r, float s) {}
  public static void vtrace2(float a, float x, int r, float s) {}
  public static void main(String[] args) {}

  public static int mainQ(int a) {
    int x, s;
    int r;
    x = a*4;
    r = 1;
    s = 13;

    while (true) {
      // assert(8*r*s - 24*a + 16*r - 12*s + 24*x - 3 == 0)
      // assert(12*(r*r) - 4*s + 1 == 0)

      // assert(2*r*s - 24*a + 16*r - 3*s + 6*x - 3 == 0)  // NEW
      // assert(12*(r*r) - s + 1 == 0)  // NEW

      vtrace1(a, x, r, s);
      if (! (x > s)) break;
      //assert(((int)(4*r*r*r - 6*r*r + 3*r) + (int)(4*x - 4*a)) == 1); 
      //assert((int)(4*s) -12*r*r == 1);
      
      //assert(((4*r*r*r - 6*r*r + 3*r) + (x - 4*a)) == 1);  // NEW
      //assert(s - 12*r*r == 1);  // NEW

      x = x - s;
      s = s + (6 * r + 3) * 4;
      r = r + 1;
    }

    // assert(8*r*s - 24*a + 16*r - 12*s + 24*x - 3 == 0)
    // assert(12*(r*r) - 4*s + 1 == 0)
    
    //assert(2*r*s - 24*a + 16*r - 3*s + 6*x - 3 == 0)  // NEW
    //assert(12*(r*r) - s + 1 == 0)  // NEW

    vtrace2(a, x, r, s);
    return r;
  }
}
