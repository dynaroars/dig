public class Egcd3 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static int mainQ(int x, int y){
	  assert(x >= 1);
	  assert(y >= 1);
     
	  int a,b,p,q,r,s,c,k,d,v;

	  a=x; b=y;  p=1;  q=0;  r=0;   s=1;

	  //assert(a==y*r+x*p); 
	  //assert(b==x*q+y*s);

	  while(true) {
	       //%%%traces: int x, int y, int a, int b, int p, int q, int r, int s
	  
	       if(!(b!=0)) break;
	       c=a;
	       k=0;
	  
	       while(true){
		    //%%%traces: int x, int y, int a, int b,  int p, int q, int r, int s, int k, int c
		    if(!(c>=b)) break;
		    d=1;
		    v=b;

		    while (true) {

			 // assert(a == y*r+x*p); 
			 // assert(b == x*q+y*s); 
			 // assert(a == k*b+c); 
			 // assert(v == b*d); 
			 //%%%traces: int x, int y, int a, int b,  int p, int q,  int r, int s, int k, int c, int d, int v
		    
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
	  return a;
     }

}
