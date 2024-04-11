public class Bresenham {
    public static void vtrace1(int X, int Y, int x, int y, int v){}
    public static void vtrace2(int X, int Y, int x, int y, int v){}    

     public static void main (String[] args) {
     }

     public static int mainQ(int X, int Y){

	 int v, x, y;
	 v = 2 * Y - X;
	 y = 0;
	 x = 0;
	 while (true) {
	     //2*Y*x - 2*X*y - X + 2*Y - v == 0
	     vtrace1(X,Y, x,y,v);
	     if (!(x <= X))
		 break;
	     
	     if (v < 0) {
		 v = v + 2 * Y;
	     } else {
		 v = v + 2 * (Y - X);
		 y++;
	     }
	     x++;
	 }
	 // 2*Y*x - 2*x*y + 2*Y - v - x + 2*y + 1 == 0
	 vtrace2(X,Y, x,y,v);
	 return 0;
     }
}
