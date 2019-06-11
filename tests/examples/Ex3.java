public class Ex3 {
    public static void vtrace1_post(int m, int tCtr){}
    public static void main (String[] args) {}
    public static int mainQ(int m){
	int tCtr = 0;
	if (m <= 0){
	    tCtr = -5;
	}
	else{  // m > 0
	    tCtr = m  + 5;
	}
	vtrace1_post(m, tCtr);
	    
	return 0;
    }
}

