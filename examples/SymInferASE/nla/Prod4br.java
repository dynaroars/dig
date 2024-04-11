public class Prod4br {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static int mainQ(int x, int y){
	  assert(x>=1);
	  assert(y>=1); 

	  int a,b,p,q;

	  a = x;
	  b = y;
	  p = 1;
	  q = 0;

	  while(true) { 
	       //assert(q+a*b*p==x*y);
	       //%%%traces: int x, int y, int a, int b, int p, int q

	       if(!(a!=0 && b!=0)) break;
	  
	       if (a % 2 ==0 && b % 2 ==0 ){
		    a = a/2;
		    b = b/2;
		    p = 4*p;
	       }
	       else if (a % 2 ==1 && b % 2 ==0 ){
		    a = a-1;
		    q = q+b*p;
	       }
	       else if (a % 2 ==0 && b % 2 ==1 ){
		    b = b-1;
		    q = q+a*p;
	       }
	       else {
		    a = a-1;
		    b = b-1;
		    q = q+(a+b+1)*p;  /*dammit I am good ---  was (a+b-1)*/
	       }
	  }

	  //assert(q == x*y);
	  return q; 
     }
}
