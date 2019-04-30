public class Fermat1 {
     public static void vtraces1(int A, int R, int u, int v, int r){}
     public static void vtraces2(int A, int R, int u, int v, int r){}
     //public static void vtraces3(int A, int R, int u, int v, int r){}
     public static void main (String[] args) {}

     public static int mainQ(int A, int R){
	  assert(A >= 1);
	  assert((R-1)*(R-1) < A);
	  assert(A <= R*R);
	  assert(A%2 ==1); 

	  int u,v,r;
	  u=2*R+1;
	  v=1;
	  r=R*R-A;


	  while (true){
	       //assert(4*(A+r) == u*u-v*v-2*u+2*v);
	       vtraces1(A, R, u, v, r);
	       if(!(r!=0)) break;
			   
	       while (true){
		    vtraces2(A, R, u, v, r);
		    if(!(r>0 )) break;
		    r=r-v;
		    v=v+2;
	       }
    
	       while (true){
		    //TODO: I think this might give prob (requires high depth?)
		    //vtraces3(A, R, u, v, r);
		    if(!(r<0 )) break;
		    r=r+u;
		    u=u+2;
	       }

	  }
  
	  //assert(u!=v); 
	  int o = (u-v)/2;
	  return o;
     }
}
