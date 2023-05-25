public class Median {
    public static void vtrace1_post(int a, int b, int c){}
    public static void main (String[] args) {}
    public static int mainQ(int a, int b, int c){
	int median;
	if((a >= b && a <= c) || (a >= c && a <= b))
	    median = a;

	else if((b >= a && b <= c) || (b >= c && b <= a))
	    median = b;
	else
	    median = c;
	
	vtrace1_post(a,b,c);	

	// vtrace1_post(a,b,c);
	// if( !( (median==a && ((b>=a && a>=c) || (c>=a && a>=b)))
	//        ||   (median==b && ((a>=b && b>=c) || (c>=b && b>=a)))
	//        ||   (median==c && ((b>=c && c>=a) || (a>=c && c>=b)))
	//        ) ){
	//     vtrace1_post(a,b,c);
	// }
	return 0;
    }
}

