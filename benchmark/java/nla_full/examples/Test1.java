public class Test1 {
     public static void vtrace1(int x, int y, int z, int b, int c){}
     public static void main (String[] args){}

     public static int mainQ(int x){
	  int y = 0;
	  int z = 0;
	  int c = 0;
	  int b = 0;
	  
	  while(true){
	       vtrace1(x, y, z, b, c);
	       if (!(c < x)) break;
    
	       c = c + 1;
	       y = y + 1;
	       if (x == 7) z = z+1;
	       z = z + 1;
	  }
	  return x;
     }
}
