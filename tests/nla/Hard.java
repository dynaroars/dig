public class Hard {

     public static void vtrace1(int A, int B,  int r, int d, int p, int q){}
     
     public static void main (String[] args) {}

     public static int mainQ(int A, int B){
	  //hardware integer division program, by Manna
	  //returns q==A//B

	  assert(A >= 0);
	  assert(B >= 1);

	  int r,d,p,q;

	  r=A;
	  d=B;
	  p=1;
	  q=0;

	  while(true){
	       if (!(r >= d)) break;
	       //assert(A >= 0 && B > 0 && q == 0 && r == A && d == B*p);
	       d = 2 * d;
	       p  = 2 * p;
	  }

	  while(true){
	       // assert(A == q*B+r && d==B*p);
	       vtrace1(A, B,  r, d, p, q);
	       if (!(p!=1)) break;
    
	       d=d/2; p=p/2;
	       if(r>=d){
		    r=r-d; q=q+p;
	       }
	  }

	  // r == A % B
	  // q == A / B
	  return q;
     }


}
