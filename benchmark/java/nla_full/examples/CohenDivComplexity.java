public class CohenDivComplexity {
     public static void vtrace1(int q, int r, int a, int b, int x, int y, int t){}

     public static void main (String[] args) {}
     

     public static int mainQ_cohendiv(int x, int y) {
	  assert(x>0 && y>0);

	  int q=0;
	  int r=x;
	  int a=0;
	  int b=0;
	  int t=0;
	  while(true) {
	       t++;
	       if(!(r>=y)) break;
	       a=1;
	       b=y;

	       while (true) {
		    t++;
		    if(!(r >= 2*b)) break;

		    a = 2*a;
		    b = 2*b;
	       }
	       r=r-b;
	       q=q+a;
	  }
	  vtrace1(q,r,a,b,x,y,t);
	  return q;
     }
}
