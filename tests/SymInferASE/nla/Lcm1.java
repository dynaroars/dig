public class Lcm1 {

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
	  v=0;


	  while(true) {
	       //assert(x*u + y*v == a*b);
	       //%%%traces: int a, int b, int x, int y, int u, int v
	       if (!(x!=y)) break;
	  

	       while (true){
		    //%%%traces: int a, int b, int x, int y, int u, int v
		    if(!(x>y)) break;
		    x=x-y;
		    v=v+u;
	       }
    
	       while (true){
		    //%%%traces: int a, int b, int x, int y, int u, int v
		    if(!(x<y)) break;
		    y=y-x;
		    u=u+v;
	       }

	  }

	  //x==gcd(a,b)
	  int r = u+v; 
	  return r; //lcm     
     }
}
