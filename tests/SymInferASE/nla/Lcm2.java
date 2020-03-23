public class Lcm2 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static int mainQ(int a, int b){
	  assert(a>=1);
	  assert(b>=1);
	  int x,y,u,v;

	  x=a;
	  y=b;
	  u=b;
	  v=a;

	  while(true) {
	       //assert(x*u + y*v == 2*a*b);
	       //%%%traces: int a, int b, int x, int y, int u, int v

	       if (!(x!=y)) break;

	       if (x>y){
		    x=x-y;
		    v=v+u;
	       }
	       else {
		    y=y-x;
		    u=u+v;
	       }
	  }

	  //x==gcd(a,b)
	  int r = (u+v)/2;
	  return r; //lcm

     }
}
