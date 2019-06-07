public class Ps1 {
    public static void vtrace1(int x, int y, int k){}
    public static void vtrace2(int x, int y, int k){}
     public static void main (String[] args){}

     public static int mainQ(int k){
	  assert (k>=0);          
	  int y = 0;
	  int x = 0;
	  int c = 0;

	  while(true){
	       vtrace1(x, y, k);
	       if (!(c < k)) break;
    
	       c = c + 1;
	       y = y + 1;
	       x = x + 1;
	  }
	  vtrace2(x,y,k);
	  return x;
     }
}
