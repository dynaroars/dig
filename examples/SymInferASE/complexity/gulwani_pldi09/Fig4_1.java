public class Fig4_1 {

     public static void main (String[] args) {
	  mainQ(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
     }

     public static int mainQ(int id, int n){
	  assert (id >= 0);
	  assert (n > id);
	  int tmp = id + 1;
	  int t = 0;

	  while(tmp != id){
	       if (tmp <= n) {
		    tmp = tmp + 1;
	       }else{
		    tmp=0;
	       }
	       t++;
	  }
	  //%%%traces: int id, int n, int t
	  //dig2: n - t + 1 == 0, -id <= 0, id - n <= -1 
	  return 0;
     }
}

