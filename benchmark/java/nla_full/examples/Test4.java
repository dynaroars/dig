public class Test4 {
    public static void vtrace1(int x, int y, int t){}

     public static void main (String[] args) {}
     
    public static int mainQ_Test4(int x, int y) {
	  assert(x>0 && y>0);
	  int i = 0;
	  int j = 0;
	  int t = 0;
	  while (i < x){
	      i++;
	      // t++;

	      while (j < y){
		  j++;
		  t++;
	      }
	      j = 0 ;
	  }

	  vtrace1(x,y,t);
	  return 0;
     }
}
