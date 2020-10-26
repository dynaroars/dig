public class Fermat1 {
    public static void vtraces1(int A, int R, int u, int v, int r){}
    public static void vtraces2(int A, int R, int u, int v, int r){}
    public static void vtraces3(int A, int R, int u, int v, int r){}    
    public static void main (String[] args) {}
	
    public static int mainQ(int A, int R){
	assert((R - 1) * (R - 1) < A);
	//assert(A <= R*R);
	assert(A % 2 ==1); 
		
	int u, v, r;
	u = 2*R + 1;
	v = 1;
	r = R*R - A;
		
		
	while (true){
	    //assert(4*(A+r) == u*u-v*v-2*u+2*v);
	    vtraces1(A, R, u, v, r);
	    if(!(r!=0)) break;
			
	    while (true){
		//assert(4*(A+r) == u*u-v*v-2*u+2*v);
		vtraces2(A, R, u, v, r);
		if(!(r>0 )) break;
		r=r-v;
		v=v+2;
	    }
			
	    while (true){
		//assert(4*(A+r) == u*u-v*v-2*u+2*v);
		vtraces3(A, R, u, v, r);
		if(!(r<0 )) break;
		r=r+u;
		u=u+2;
	    }
			
	}
	return (u-v)/2;
    }
}
