public class Lcm1 {
    public static void vtrace1(int a, int b, int x, int y, int u, int v){}
    public static void vtrace2(int a, int b, int x, int y, int u, int v){}
    public static void vtrace3(int a, int b, int x, int y, int u, int v){}
    public static void vtrace4(int a, int b, int x, int y, int u, int v){}
			   
    public static void main (String[] args) {}
    public static int mainQ(int a, int b){
	assert(a >= 1);
	assert(b >= 1);
	int x,y,u,v;
	x=a;
	y=b;
	u=b;
	v=0;

	while(true) {
	    //assert(x*u + y*v == a*b);
	    vtrace1(a, b, x, y, u, v);
	    if (!(x != y)) break;
	  
	    while (true){
		//assert(x*u + y*v == a*b);
		vtrace2(a, b, x, y, u, v);
		if(!(x > y)) break;
		x = x - y;
		v = v + u;
	    }
    
	    while (true){
		//assert(x*u + y*v == a*b);
		vtrace3(a, b, x, y, u, v);
		if(!(x < y)) break;
		y = y - x;
		u = u + v;
	    }
	}

	//x==gcd(a,b)
	//a*b == u*y + v*y
	vtrace4(a,b,x,y,u,v);

	return u+v; //lcm     
    }
}


