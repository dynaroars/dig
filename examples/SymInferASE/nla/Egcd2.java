public class Egcd2 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static int mainQ(int x, int y){
	  assert(x>=1);
	  assert(y>=1);
     
	  int a,b,p,q,r,s,c,k;

	  a=x;
	  b=y;
	  p=1;
	  q=0;
	  r=0; 
	  s=1;
	  c=0;
	  k=0;
	  while(true) {
	       //%%%traces: int x, int y, int a, int b, int p, int q, int r, int s, int c, int k
	       if(!(b!=0)) break;
	       c=a;
	       k=0;

	       while(true){
		    //assert(a == k*b+c);
		    //assert(a == y*r+x*p);
		    //assert(b == x*q+y*s);
		    //%%%traces: int x, int y, int a, int b, int p, int q, int r, int s, int c, int k
		    if(!( c>=b )) break;
		    c=c-b;
		    k=k+1;
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

