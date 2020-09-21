public class Egcd3_1loc {

    // public static void vtrace1(int x, int y, int a, int b,
    // 			       int p, int q,  int r, int s){}

    // public static void vtrace2(int x, int y, int a, int b,
    // 			       int p, int q,  int r, int s,
    // 			       int k, int c){}
     
    public static void vtrace3(int x, int y, int a, int b,
			       int p, int q,  int r, int s,
			       int k, int c, int d, int v){}

    public static void vtrace4(int x, int y, int a, 
			       int p, int q,  int r, int s){}
			       

    public static void main (String[] args) {
	//mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
    }

    public static int mainQ(int x, int y){
	assert(x >= 1);
	assert(y >= 1);
     
	int a=0, b=0, p=0, q=0, r=0, s=0, c=0, k=0, d=0, v=0;

	a=x; b=y; p=1; q=0; r=0; s=1;

	//assert(a==y*r+x*p); 
	//assert(b==x*q+y*s);

	while(true) {
	    //vtrace1(x, y, a, b, p , q, r, s);
	    
	    if(!(b!=0)) break;

	    c=a;
	    k=0;
	  
	    while(true){
		//vtrace2(x, y, a, b,  p, q,  r, s, k, c);
		
		if(!(c>=b)) break;
		d=1;
		v=b;

		while (true) {
		    // assert(a == y*r+x*p); 
		    // assert(b == x*q+y*s); 
		    // assert(a == k*b+c); 
		    // assert(v == b*d); 
		    vtrace3(x, y, a, b,  p, q,  r, s, k, c, d, v);
		    
		    if(!( c>= 2*v )) break;
		    d = 2*d;
		    v = 2*v;
		}
		c=c-v;
		k=k+d;
	    }
      
	    a=b;
	    b=c;
	    int temp;
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
