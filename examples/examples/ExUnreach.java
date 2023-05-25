public class ExUnreach {
    //public static void vtrace0(int m){}
    public static void vtrace1(int m){}
    public static void main (String[] args) {}
    public static int mainQ(int m){
		assert(m >= 1);
		//if (m < 0){ //not reachable
		//    vtrace0(m);
		//}
		//else{
		    //vtrace1(m);
		//}
		vtrace1(m);
	return 0;
    }
}

