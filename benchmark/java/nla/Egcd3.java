public class Egcd3 {
	
	// public static void vtrace1(int x, int y, int a, int b,
	// int p, int q,  int r, int s){}
	
	// public static void vtrace2(int x, int y, int a, int b,
	// int p, int q,  int r, int s,
	// int c, int k){}
	
	public static void vtrace3( int x, int y, int a, int b,
	int p, int q,  int r, int s,
	int c, int k, int d, int v){}
	
	//public static void vtrace4(int x, int y, int a, 
	//int p, int q,  int r, int s){}
	
	
	public static void main (String[] args) {
		//mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
	}
	
	public static int mainQ(int x, int y){
		assert(x >= 1);
		assert(y >= 1);
		
		int a=x;
		int b=y;
		int p=1;
		int q=0;
		int r=0;
		int s=1;
		int c=0;
		int k=0;
		int d=0;
		int v=0;
		int temp=0;
		//assert(a==y*r+x*p); 
		//assert(b==x*q+y*s);
		while(true) {
			//vtrace1(x, y, a, b, p , q, r, s);
			
			if(!(b!=0)) break;
			
			c=a;
			k=0;
			
			while(true){
				//vtrace2(x, y, a, b,  p, q,  r, s, c, k);
				
				if(!(c>=b)) break;
				d=1;
				v=b;
				
				while (true) {
					// assert(a == y*r+x*p); 
					// assert(b == x*q+y*s); 
					// assert(a == k*b+c); 
					// assert(v == b*d); 
					vtrace3(x, y, a, b,  p, q,  r, s, c, k, d, v);
					if(!( c>= 2*v )) break;
					d = 2*d;
					v = 2*v;
				}
				c=c-v;
				k=k+d;
			}
			
			a=b;
			b=c;
			temp=p;
			p=q;
			q=temp-q*k;
			temp=r;
			r=s;
			s=temp-s*k;
		}
		
		
		//don't track b, which is guaranteed to be 0
		//vtrace4(x,y,a,p,q,r,s);
		return a;
	}
	
}
