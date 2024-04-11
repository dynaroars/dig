public class Sqrt1 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]));
     }

     public static int mainQ(int n){
	  assert(n >= 0);
  
	  int a,s,t;
	  a=0;
	  s=1;
	  t=1;

	  int ctr = 0;
	  while(true){
	       //assert(a*a <= n);
	       //assert(t == 2*a + 1);
	       //assert(s == (a + 1)*(a + 1));
	       //the above 2 should be equiv to t^2 - 4*s + 2*t + 1 == 0
	  
	       //%%%traces: int a, int n, int t, int s 
	       if(!(s <= n)) break;
	       a=a+1;
	       t=t+2;
	       s=s+t;
	  }

	  return a;
     
     }
}
