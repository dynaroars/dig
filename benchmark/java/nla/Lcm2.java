public class Lcm2 {
	public static void vtrace1(int a, int b, int x, int y, int u, int v){}
	///public static void vtrace2(int a, int b, int x, int y, int u, int v){}    
	public static void main (String[] args) {}
	
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
			vtrace1(a, b, x, y, u, v);
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
		//assert(2*a*b - u*y - v*y == 0);
		//vtrace2(a, b, x, y, u, v);
		//x==gcd(a,b)
		//(u+v)/2 == lcm(a,b);
		return (u+v)/2;
		
	}
}
